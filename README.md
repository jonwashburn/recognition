# recognition

[![CI](https://github.com/jonwashburn/recognition/actions/workflows/ci.yml/badge.svg)](https://github.com/jonwashburn/recognition/actions/workflows/ci.yml)

Single-file executable monolith (Lean 4) for the Recognition project.

## Quick start

1) Install elan (Lean toolchain manager):

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
source "$HOME/.elan/env"
```

2) Build:

```bash
lake build
```

3) CI smoke (fast):

```bash
lake exe ci_checks
```

### Certificates Manifest

See `CERTIFICATES.md` for a copy/paste list of `#eval` commands that elaborate the certificates and print concise OK lines. For a single consolidated line per cert, run:

```lean
#eval IndisputableMonolith.URCAdapters.certificates_manifest
```

## Notes

- The repository includes a GitHub Actions workflow that installs elan, builds the project, runs a smoke check, and guards against `sorry`/`admit` outside the heavy monolith file.
- For monolith exploration, open `IndisputableMonolith.lean` in your editor with Lean support enabled.

## Syncing the monolith from a canonical source

Use the helper script to copy a canonical `IndisputableMonolith.lean` here and commit it:

```bash
./scripts/sync_monolith_from.sh /absolute/path/to/IndisputableMonolith.lean
git push
```


