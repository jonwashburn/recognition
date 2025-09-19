#!/usr/bin/env python3
import argparse, json, re, sys, pathlib

def find_namespaces(text: str):
    # Very simple namespace scanner: matches lines like `namespace Foo` until `end Foo`.
    # Fallback: coarse ranges; a human/agent will refine.
    ns_re = re.compile(r'^(namespace\s+([A-Za-z0-9_.]+))', re.M)
    ends_re = re.compile(r'^end\s+([A-Za-z0-9_.]+)', re.M)
    starts = [(m.start(), m.group(2)) for m in ns_re.finditer(text)]
    ends = [(m.start(), m.group(1)) for m in ends_re.finditer(text)]
    # Build naive ranges by order
    ranges = []
    stack = []
    for pos, name in sorted(starts + ends, key=lambda x: x[0]):
        line = text[:pos].count('\n') + 1
        if (pos, name) in starts:
            stack.append((name, line))
        else:
            if stack:
                sname, sline = stack.pop()
                if sname == name:
                    ranges.append({
                        'name': name,
                        'start_line': sline,
                        'end_line': line
                    })
    return ranges

def chunk_by_lines(ranges, min_lines, max_lines):
    out = []
    for r in ranges:
        span = max(0, r['end_line'] - r['start_line'] + 1)
        if span == 0:
            continue
        if span <= max_lines and span >= min_lines:
            out.append(r)
        elif span > max_lines:
            # Split large ranges into pseudo-chunks by equal sizes
            parts = (span + max_lines - 1) // max_lines
            size = span // parts
            s = r['start_line']
            for i in range(parts):
                e = s + size - 1
                if i == parts - 1:
                    e = r['end_line']
                out.append({'name': r['name'] + f"#part{i+1}", 'start_line': s, 'end_line': e})
                s = e + 1
        # small ranges below min_lines are ignored for now
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', default='IndisputableMonolith.lean')
    ap.add_argument('--min-lines', type=int, default=60)
    ap.add_argument('--max-lines', type=int, default=220)
    ap.add_argument('--out', default='scripts/swarm/queue.json')
    args = ap.parse_args()

    p = pathlib.Path(args.source)
    text = p.read_text(encoding='utf-8')
    ranges = find_namespaces(text)
    chunks = chunk_by_lines(ranges, args.min_lines, args.max_lines)

    # Filter out heavy patterns by name heuristics
    blocked = [
        'IndisputableMonolith.Recognition',
        'IndisputableMonolith.Dynamics',
        'IndisputableMonolith.ClassicalBridge',
        'IndisputableMonolith.URC',
    ]
    def allowed(c):
        return all(not c['name'].startswith(b) for b in blocked)

    jobs = [c for c in chunks if allowed(c)]

    pathlib.Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, 'w', encoding='utf-8') as f:
        json.dump({'source': args.source, 'jobs': jobs}, f, indent=2)
    print(f"Wrote {len(jobs)} jobs to {args.out}")

if __name__ == '__main__':
    main()


