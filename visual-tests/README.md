# Visual Tests

A lightweight visual regression harness for PostMeta.

## Layout

```
visual-tests/
├── run.py       # runner: renders every case with the CLI, writes a report
├── index.html   # report viewer (current vs. baseline vs. reference)
├── cases/       # tracked .mp fixture corpus (304 cases)
└── generated/   # untracked outputs
    ├── current/     # SVGs from the latest run
    ├── baseline/    # blessed snapshots (bless locally)
    └── report.json  # per-case results and metadata
```

## Sources

Cases are adapted from the public MetaPost examples page:

- http://www.tlhiv.org/MetaPost/examples/examples.html

## Usage

Run all cases and generate current outputs plus a report:

```bash
python3 visual-tests/run.py
```

Bless current outputs as baseline snapshots (do this on a known-good
tree before starting a change; the baseline stays local):

```bash
python3 visual-tests/run.py --bless
```

Run a subset:

```bash
python3 visual-tests/run.py --filter 33
```

A case FAILS when the CLI exits non-zero, produces no SVG, or prints an
`Error:` diagnostic; for passing cases the report also records whether
the SVG matches the blessed baseline byte-for-byte (`matches_baseline`).

Open `visual-tests/index.html` in a browser (served from this directory)
to compare current output, baseline, and the tlhiv reference images.
