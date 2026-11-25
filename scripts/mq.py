"""Stage 5: lock updates as pull requests into proto-installer-mq, serialised by GitHub merge queue.

One branch per policy (lock-a, lock-d, lock-e), each holding lock/modules/<module>.json and
lock/state.json. The build logic is the Stage 4b integrator's (integrate.py, copied): one
dependency order, reuse of published versions, published-asset hashes, staging failures abort.

  compute      build the candidate for one event and open the lock PR(s)
  check        lock-check: verify a candidate tree (hashes, unbuilt pairs, one version, policy)
  queue-event  react to a lock PR leaving the queue (merged or removed)
  assemble     write a single lock.json from a lock directory (for module builds)

A held change is an open PR labelled `held`, never enqueued: it is the visible record and the
only place the hold lives. The base branch never carries held state.
"""
import argparse
import base64
import copy
import datetime as dt
import hashlib
import io
import json
import os
import subprocess
import sys
import time
import urllib.request
import zipfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import integrate as I  # noqa: E402

OWNER = I.OWNER
REPO = I.LOCK_REPO
HOLD_MINUTES = 15
MODULE_REPOS = ["proto-BHoM", "proto-BHoM_Engine", "proto-BHoM_Adapter",
                "proto-Excel_Toolkit", "proto-PowerPoint_Toolkit", "proto-HTTP_Toolkit"]
META_OPEN, META_CLOSE = "<!-- lock-meta ", " -->"


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(cmd: list[str], check: bool = True, cwd: str | None = None) -> str:
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=cwd)
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd[:4])} failed: {r.stdout.strip()} {r.stderr.strip()}")
    return r.stdout


def api(path: str, method: str = "GET", fields: list[str] | None = None):
    cmd = ["gh", "api", "-X", method, path] + (fields or [])
    out = run(cmd)
    return json.loads(out) if out.strip() else None


def read_lock(d: Path) -> tuple[dict, dict]:
    modules = {f.stem: json.loads(f.read_text(encoding="utf-8")) for f in sorted((d / "modules").glob("*.json"))}
    state = json.loads((d / "state.json").read_text(encoding="utf-8"))
    state.setdefault("dropped", {})
    state.setdefault("held", {})
    return {"core": None, "modules": modules}, state


def write_lock(d: Path, lock: dict, state: dict) -> None:
    md = d / "modules"
    md.mkdir(parents=True, exist_ok=True)
    for f in md.glob("*.json"):
        if f.stem not in lock["modules"]:
            f.unlink()
    for m, e in lock["modules"].items():
        (md / f"{m}.json").write_text(json.dumps(e, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    (d / "state.json").write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def meta_of(body: str | None) -> dict:
    body = body or ""
    i = body.find(META_OPEN)
    if i < 0:
        return {}
    j = body.find(META_CLOSE, i)
    return json.loads(body[i + len(META_OPEN):j])


def open_prs(branch: str) -> list[dict]:
    return api(f"repos/{OWNER}/{REPO}/pulls?state=open&base={branch}&per_page=100") or []


def held_prs(branch: str) -> dict[str, dict]:
    held = {}
    for p in open_prs(branch):
        if any(l["name"] == "held" for l in p["labels"]):
            m = meta_of(p["body"])
            for u, h in m.get("held", {}).items():
                held[u] = dict(h, pr=p["number"], since=p["created_at"])
    return held


def series(module: str, sha: str, lock: dict):
    """Members of the change unit, from Depends-On links in the merged PR behind sha.
    Stateless: a dependent merged first is found again from the upstream's own event."""
    pr = I.pr_for(module, sha)
    blame = [{"repo": module, "sha": sha, "pr": pr["number"] if pr else None}]
    members = {module: sha}
    if not pr:
        return members, blame, "single"
    links = I.depends_links(pr["body"])
    unmerged = [f"{o}/{r}#{n}" for o, r, n in links if not I.pr_merged(o, r, n)]
    if unmerged:
        return None, blame, f"series waiting on {', '.join(unmerged)}"
    for o, r, n in links:
        if o == OWNER and r != module:
            members[r] = I.head_of(r)
            blame.append({"repo": r, "sha": members[r], "pr": n})
    for r in MODULE_REPOS:
        if r in members:
            continue
        for p in api(f"repos/{OWNER}/{r}/pulls?state=closed&sort=updated&direction=desc&per_page=20") or []:
            if p.get("merged_at") and (OWNER, module, pr["number"]) in I.depends_links(p.get("body") or ""):
                head = I.head_of(r)
                if lock["modules"].get(r, {}).get("sha") != head:
                    members[r] = head
                    blame.append({"repo": r, "sha": head, "pr": p["number"]})
    return members, blame, "series" if len(members) > 1 else "single"


def attempt(lock: dict, state: dict, changes: dict[str, str], blame: list, mode: str) -> dict:
    """Stage 4b attempt() semantics, returning a proposal instead of writing a lock."""
    overlay: dict[str, dict] = {}
    retry = {m: d["sha"] for m, d in state["dropped"].items()}
    for m in changes:
        if any(d not in lock["modules"] and d not in changes for d in I.deps_of(m, changes[m])):
            return {"outcome": "deferred: upstream not in lock"}
    order = I.build_order(changes, I.dependents(lock["modules"], set(changes), retry), lock, retry)
    failing: list[str] = []
    excluded: set[str] = set()
    for x in order:
        if x in excluded:
            continue
        sha = changes.get(x) or (lock["modules"][x]["sha"] if x in lock["modules"] else retry[x])
        st = I.stage_for(x, sha, lock, overlay)
        e = I.build(x, sha, st) if st is not None else {"ok": False, "reason": "upstream missing"}
        if e["ok"]:
            overlay[x] = e
            continue
        if x in changes:
            return {"outcome": "own build failed", "failing": [x], "order": order}
        failing.append(x)
        if mode == "hold":
            return {"outcome": "held", "failing": failing, "order": order}
        excluded |= {x} | set(I.dependents({**lock["modules"], **overlay}, {x}, retry))
    new_lock, new_state = copy.deepcopy(lock), copy.deepcopy(state)
    for x in excluded:
        sha = lock["modules"][x]["sha"] if x in lock["modules"] else retry[x]
        new_lock["modules"].pop(x, None)
        overlay.pop(x, None)
        new_state["dropped"].setdefault(x, {"sha": sha, "since": now(), "because": blame})
    for m, e in overlay.items():
        new_lock["modules"][m] = e
        new_state["dropped"].pop(m, None)
    bad = I.unbuilt_pairs(new_lock)
    if bad:
        raise RuntimeError("refusing to propose a lock with unbuilt pairs: " + "; ".join(bad))
    return {"outcome": "advanced" if not excluded else "advanced, dependents dropped",
            "lock": new_lock, "state": new_state, "order": order, "failing": failing,
            "dropped": sorted(excluded), "advanced": sorted(overlay)}


def git_auth() -> list[str]:
    tok = os.environ["APP_TOKEN"]
    basic = base64.b64encode(f"x-access-token:{tok}".encode()).decode()
    return ["-c", f"http.extraheader=AUTHORIZATION: basic {basic}"]


def clone(branch: str, dest: Path) -> None:
    run(["git", *git_auth(), "clone", "-q", "--depth", "1", "--branch", branch,
         f"https://github.com/{OWNER}/{REPO}.git", str(dest)])


def open_pr(branch: str, base_dir: Path, lock: dict, state: dict, title: str, meta: dict,
            text: str, labels: list[str], enqueue: bool) -> int:
    head = f"lockpr/{branch}/{meta['event_module']}-{meta['event_sha'][:8]}-{os.environ.get('GITHUB_RUN_ID', 'local')}-{int(time.time())}"
    write_lock(base_dir / "lock", lock, state)
    g = ["git", "-C", str(base_dir)]
    run(g + ["checkout", "-q", "-b", head])
    run(g + ["add", "-A", "lock"])
    run(g + ["-c", "user.name=proto-lock-bot", "-c", "user.email=proto-lock-bot@users.noreply.github.com",
             "commit", "-q", "-m", title])
    run(["git", "-C", str(base_dir), *git_auth(), "push", "-q", "origin", head])
    body = text + "\n\n" + META_OPEN + json.dumps(meta, sort_keys=True) + META_CLOSE
    out = run(["gh", "pr", "create", "-R", f"{OWNER}/{REPO}", "--base", branch, "--head", head,
               "--title", title, "--body", body])
    number = int(out.strip().rsplit("/", 1)[-1])
    for lab in labels:
        run(["gh", "pr", "edit", str(number), "-R", f"{OWNER}/{REPO}", "--add-label", lab])
    if enqueue:
        r = subprocess.run(["gh", "pr", "merge", str(number), "-R", f"{OWNER}/{REPO}", "--auto"],
                           capture_output=True, text=True)
        print(json.dumps({"enqueue": number, "rc": r.returncode, "out": (r.stdout + r.stderr).strip()}))
        if r.returncode != 0:
            raise RuntimeError(f"enqueue of #{number} failed: {r.stderr.strip()}")
    return number


def compute(policy: str, module: str, kind: str, work: Path) -> dict:
    branch = f"lock-{policy}"
    base = work / branch
    clone(branch, base)
    lock, state = read_lock(base / "lock")
    held = held_prs(branch)
    mode = "drop" if policy == "d" else "hold"
    rec = {"t": now(), "policy": policy, "kind": kind, "module": module}
    if kind == "timer":
        due = {u: h for u, h in held.items()
               if dt.datetime.now(dt.timezone.utc) - dt.datetime.strptime(h["since"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
               >= dt.timedelta(minutes=HOLD_MINUTES)}
        if policy != "e" or not due:
            return dict(rec, outcome="timer: nothing due")
        u, h = next(iter(due.items()))
        res = attempt(lock, state, {u: h["sha"]}, h["blame"], "drop")
        meta = {"event_module": u, "event_sha": h["sha"], "changes": {u: h["sha"]}, "supersedes": [h["pr"]],
                "outcome": res["outcome"], "order": res.get("order"), "dropped": res.get("dropped", [])}
        n = open_pr(branch, base, res["lock"], res["state"], f"lock-{policy}: E hold expired, advance {u}, drop {', '.join(res.get('dropped', [])) or 'none'}",
                    meta, f"E hold of {HOLD_MINUTES} min expired for #{h['pr']}. Supersedes #{h['pr']} when merged.", ["lock-update"], True)
        return dict(rec, outcome=res["outcome"], pr=n, supersedes=h["pr"])
    sha = I.head_of(module)
    if lock["modules"].get(module, {}).get("sha") == sha:
        return dict(rec, outcome=f"skip: {module}@{sha[:8]} already in lock-{policy}")
    if any(h["sha"] == sha and u == module for u, h in held.items()):
        return dict(rec, outcome=f"skip: {module}@{sha[:8]} is held (#{held[module]['pr']})")
    changes, blame, note = series(module, sha, lock)
    if changes is None:
        return dict(rec, outcome=note)
    joint = []
    if mode == "hold":
        for u, h in held.items():
            if u not in changes and any(u in I.upstreams(x, changes[x], lock) for x in changes):
                changes[u] = h["sha"]
                joint.append(u)
    res = attempt(lock, state, changes, blame, mode)
    meta = {"event_module": module, "event_sha": sha, "changes": changes, "blame": blame, "note": note,
            "outcome": res["outcome"], "order": res.get("order"), "failing": res.get("failing", []),
            "dropped": res.get("dropped", []), "supersedes": [held[u]["pr"] for u in joint]}
    if res["outcome"].startswith("deferred"):
        return dict(rec, outcome=res["outcome"], changes=changes)
    if res["outcome"] in ("held", "own build failed"):
        held_state = copy.deepcopy(state)
        for m in changes:
            held_state["held"][m] = {"sha": changes[m], "blame": blame, "reason": f"{res['outcome']}: {', '.join(res['failing'])}"}
        meta["held"] = held_state["held"]
        n = open_pr(branch, base, lock, held_state, f"lock-{policy}: HELD {', '.join(sorted(changes))} (breaks {', '.join(res['failing'])})",
                    meta, f"Held under policy {policy.upper()}: {res['outcome']} ({', '.join(res['failing'])}). Blame: "
                    + ", ".join(f"{b['repo']}#{b['pr']}" for b in blame) + ". Not enqueued; this open PR is the record of the hold.",
                    ["lock-update", "held"], False)
        return dict(rec, outcome=res["outcome"], pr=n, failing=res["failing"])
    n = open_pr(branch, base, res["lock"], res["state"],
                f"lock-{policy}: {res['outcome']}: {', '.join(sorted(changes))}" + (f" (joint with held {', '.join(joint)})" if joint else ""),
                meta, f"Integrates {', '.join(f'{m}@{s[:8]}' for m, s in sorted(changes.items()))}. Build order: {' -> '.join(res['order'])}."
                + (f" Dropped: {', '.join(res['dropped'])}." if res["dropped"] else "")
                + (f" Supersedes held #{', #'.join(str(x) for x in meta['supersedes'])} when merged." if joint else ""),
                ["lock-update"], True)
    return dict(rec, outcome=res["outcome"], pr=n, joint=joint, order=res["order"])


def check(d: Path, labels: list[str]) -> int:
    lock, state = read_lock(d)
    errors: list[str] = []
    if "held" in labels:
        errors.append("this PR is labelled held: a held change cannot merge")
    if state.get("held"):
        errors.append(f"state lists held changes {sorted(state['held'])}: a held change cannot merge")
    payload: dict[str, dict[str, str]] = {}
    for m, e in sorted(lock["modules"].items()):
        try:
            with urllib.request.urlopen(e["url"]) as resp:
                data = resp.read()
        except Exception as exc:  # report every unreachable asset, then fail
            errors.append(f"{m}: asset unreachable ({exc})")
            continue
        if hashlib.sha256(data).hexdigest() != e["sha256"]:
            errors.append(f"{m}: published asset hash differs from the lock")
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for info in z.infolist():
                if not info.is_dir():
                    payload.setdefault(info.filename.lower(), {})[m] = hashlib.sha256(z.read(info)).hexdigest()[:12]
        for dep in e.get("built_against", {}).get("deps", {}):
            if dep not in lock["modules"]:
                errors.append(f"{m}: upstream {dep} is not in the lock")
    errors += [f"unbuilt pair: {p}" for p in I.unbuilt_pairs(lock)]
    for f, by_module in sorted(payload.items()):
        if len(set(by_module.values())) > 1:
            errors.append(f"one-version: {f} differs between " + ", ".join(f"{m} ({h})" for m, h in sorted(by_module.items())))
    for x in state["dropped"]:
        if x in lock["modules"]:
            errors.append(f"{x} is both dropped and in the lock")
    summary = [f"lock-check: {len(lock['modules'])} modules, {len(payload)} files, {len(errors)} errors"] + [f"- {e}" for e in errors]
    print("\n".join(summary))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        Path(os.environ["GITHUB_STEP_SUMMARY"]).write_text("\n".join(summary) + "\n", encoding="utf-8")
    for e in errors:
        print(f"::error title=lock-check::{e}")
    return 1 if errors else 0


def removal_reason(number: int) -> str:
    q = ('query($o:String!,$r:String!,$n:Int!){repository(owner:$o,name:$r){pullRequest(number:$n){'
         'timelineItems(last:10,itemTypes:[REMOVED_FROM_MERGE_QUEUE_EVENT]){nodes{... on RemovedFromMergeQueueEvent{reason createdAt}}}}}}')
    out = run(["gh", "api", "graphql", "-f", f"query={q}", "-f", f"o={OWNER}", "-f", f"r={REPO}", "-F", f"n={number}"], check=False)
    try:
        nodes = json.loads(out)["data"]["repository"]["pullRequest"]["timelineItems"]["nodes"]
        return json.dumps(nodes[-1]) if nodes else "none recorded"
    except Exception as exc:
        return f"unavailable ({exc}): {out[:200]}"


def queue_event(number: int, action: str) -> None:
    p = api(f"repos/{OWNER}/{REPO}/pulls/{number}")
    m = meta_of(p["body"])
    if action == "closed":
        if p.get("merged_at"):
            for old in m.get("supersedes", []):
                run(["gh", "pr", "close", str(old), "-R", f"{OWNER}/{REPO}", "--comment", f"Superseded by #{number}, merged."], check=False)
            print(json.dumps({"merged": number, "closed_superseded": m.get("supersedes", [])}))
        return
    for _ in range(12):  # a PR that merged from the queue is also dequeued; give the merge time to show
        if p.get("merged_at") or p["state"] != "open":
            print(json.dumps({"dequeued": number, "merged_or_closed": True}))
            return
        time.sleep(10)
        p = api(f"repos/{OWNER}/{REPO}/pulls/{number}")
    reason = removal_reason(number)
    print(json.dumps({"removed_from_queue": number, "reason": reason}))
    if any(l["name"] == "held" for l in p["labels"]):
        return
    policy = p["base"]["ref"].removeprefix("lock-")
    run(["gh", "pr", "close", str(number), "-R", f"{OWNER}/{REPO}", "--comment",
         f"Removed from the merge queue ({reason}). Recomputing against the current lock-{policy}."], check=False)
    api(f"repos/{OWNER}/{REPO}/dispatches", "POST",
        ["-f", "event_type=recompute", "-f", f"client_payload[module]={m['event_module']}", "-f", f"client_payload[policies]={policy}"])


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("compute")
    c.add_argument("--kind", required=True, choices=["module", "recompute", "timer"])
    c.add_argument("--module", default="")
    c.add_argument("--policies", default="a,d,e")
    k = sub.add_parser("check")
    k.add_argument("--dir", required=True)
    k.add_argument("--labels", default="")
    q = sub.add_parser("queue-event")
    q.add_argument("--pr", type=int, required=True)
    q.add_argument("--action", required=True, choices=["dequeued", "closed"])
    s = sub.add_parser("assemble")
    s.add_argument("--dir", required=True)
    s.add_argument("--out", required=True)
    a = ap.parse_args()
    if a.cmd == "check":
        sys.exit(check(Path(a.dir), [x for x in a.labels.split(",") if x]))
    if a.cmd == "assemble":
        lock, _ = read_lock(Path(a.dir))
        Path(a.out).write_text(json.dumps(lock), encoding="utf-8")
        return
    if a.cmd == "queue-event":
        queue_event(a.pr, a.action)
        return
    work = Path(os.environ.get("RUNNER_TEMP", ".")) / "mq-work"
    work.mkdir(parents=True, exist_ok=True)
    records = []
    try:
        for p in [x.strip() for x in a.policies.split(",") if x.strip()]:
            records.append(compute(p, a.module, a.kind, work))
    except I.StagingError as err:
        print(f"::error title=staging failed, nothing proposed::{err}")
        sys.exit(1)
    for r in records:
        print(json.dumps(r, sort_keys=True))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        Path(os.environ["GITHUB_STEP_SUMMARY"]).write_text("\n".join(json.dumps(r) for r in records) + "\n", encoding="utf-8")
    with open(work / "timings.jsonl", "a") as f:
        f.write(json.dumps({"t": now(), "run_id": os.environ.get("GITHUB_RUN_ID"), "builds": I.BUILDS}) + "\n")
    print("timings: " + json.dumps(I.BUILDS))


if __name__ == "__main__":
    main()
