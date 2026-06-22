# Project: curve-trees

## Crate layout

This repo is a Cargo workspace. The four core crates are local subdirectories — **no Cargo.lock lookup needed**:

| Crate | Path |
|---|---|
| `bulletproofs` | `bulletproofs/src/` |
| `relations` | `relations/src/` |
| `ark-dlog-gadget` | `ark-dlog-gadget/src/` |
| `ark-ec-divisors` | `ark-ec-divisors/src/` |

Read or grep these directly using their workspace-relative path.

## External Dependency Source Lookup

**Never spawn an agent or run `find /` to locate a dependency's source.**

Only two external git repos are depended on. Both share the same `~/.cargo/git/checkouts/` lookup pattern.

### Step 1 — Derive rev and slug from Cargo.lock (once per session)

```bash
# arkworks-algebra: get rev (7-char prefix)
grep -A3 'name = "ark-ff"' Cargo.lock | grep source | grep -o '#[0-9a-f]*' | cut -c2-8

# arkworks-algebra: get slug
ls ~/.cargo/git/checkouts/ | grep arkworks-algebra

# crypto (dock_crypto_utils / dock_merlin): get rev
grep -A3 'name = "dock_crypto_utils"' Cargo.lock | grep source | grep -o '#[0-9a-f]*' | cut -c2-8

# crypto: get slug
ls ~/.cargo/git/checkouts/ | grep -v arkworks | grep crypto
```

Run these once and keep the slug+rev pair for the rest of the session. Full path is `~/.cargo/git/checkouts/<SLUG>/<REV>/`.

### Step 2 — Subdirectory layout

| Crates | Git repo name | Subdirectory layout |
|---|---|---|
| `ark-ff`, `ark-ec`, `ark-serialize`, `ark-poly`, `ark-pallas`, `ark-vesta`, `ark-selene`, `ark-helios`, `ark-wei25519`, `ark-curve25519`, `ark-ed25519`, `ark-secp256k1`, `ark-secq256k1`, `ark-host-msm` | `arkworks-algebra` | `ff/src/`, `ec/src/`, `serialize/src/`, `poly/src/`, `curves/<CURVE>/src/`, `host-msm/src/` |
| `dock_crypto_utils`, `dock_merlin` | `crypto` | `utils/src/`, `merlin/src/` |

### Step 3 — Symbol lookup

```bash
# After deriving SLUG and REV (e.g. REV=8d51050):
grep -rn "SymbolName" ~/.cargo/git/checkouts/<SLUG>/<REV>/ec/src/
```

**Never hardcode a revision hash** — always derive it from Cargo.lock at the start of the task. A hardcoded rev that drifts from Cargo.lock produces wrong paths silently.

## Running tests

Use `cargo nextest run --release` for large or many tests. Prefer nextest over `cargo test`.

```bash
cargo nextest run --release -p bulletproofs
cargo nextest run --release -p relations
```

## Bash tool hygiene

**Write one command per Bash call, starting with the actual tool.** Permission matching is on the first token only — it does not cross `&&`, `;`, or `|`. Patterns to avoid:

```bash
# BAD — cd preamble, permission match stops at 'cd':
cd <workspace> && grep -rn "Symbol" bulletproofs/src

# BAD — shell variable preamble:
REV=8d51050
grep -n "fn foo" ~/.cargo/git/checkouts/<SLUG>/${REV}/ff/src/lib.rs

# GOOD — workspace-relative path, starts with the tool:
grep -rn "Symbol" bulletproofs/src
grep -n "fn foo" ~/.cargo/git/checkouts/<SLUG>/8d51050/ff/src/lib.rs
```

**Prefer the `Read` tool over `sed -n '/pattern/,/}/p'`** for extracting a section of a file — it takes `offset` and `limit` line numbers and needs no shell.
