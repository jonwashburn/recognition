#!/usr/bin/env python3
import argparse, json, os, sys, time
from pathlib import Path

try:
    import fcntl  # type: ignore
except Exception:
    fcntl = None

def lock_file(fp):
    if fcntl is None:
        return
    fcntl.flock(fp.fileno(), fcntl.LOCK_EX)

def unlock_file(fp):
    if fcntl is None:
        return
    fcntl.flock(fp.fileno(), fcntl.LOCK_UN)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--queue', default='scripts/swarm/queue.json')
    ap.add_argument('--agent', default=os.environ.get('AGENT_ID', 'agent'))
    args = ap.parse_args()

    qpath = Path(args.queue)
    if not qpath.exists():
        print(json.dumps({'error': f'queue not found: {qpath}'}))
        sys.exit(1)

    # Lock, read, claim, write back
    with open(qpath, 'r+', encoding='utf-8') as fp:
        lock_file(fp)
        try:
            data = json.load(fp)
            jobs = data.get('jobs', [])
            claimed_idx = None
            now = int(time.time())
            for i, j in enumerate(jobs):
                if not j.get('claimedBy'):
                    j['claimedBy'] = args.agent
                    j['claimedAt'] = now
                    claimed_idx = i
                    break
            if claimed_idx is None:
                print(json.dumps({'status': 'empty'}))
                return
            # rewind & write back
            fp.seek(0)
            fp.truncate(0)
            json.dump(data, fp, indent=2)
        finally:
            unlock_file(fp)

    job = jobs[claimed_idx]
    print(json.dumps({'status': 'ok', 'job': job, 'source': data.get('source', 'IndisputableMonolith.lean')}))

if __name__ == '__main__':
    main()


