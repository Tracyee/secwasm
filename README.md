# secwasm Project - Oct 2023

- Implementation of a security-typesystem following [this](https://plas2022.github.io/files/pdf/SecWasm.pdf) paper
- Security guarantee: termination-insensitive non-interference

## Setup

### Nix setup
- Running `nix-shell` will enter an environment with the required dependencies.
- Otherwise, the following manual setup is possible

### Dependencies
- Ocaml version 5, `dune` version 3.10
- Webassembly binary toolkit: `wabt`, provides `wat2wasm` and `wasm2wat` among others
- wasmtime
- Nodejs: version 18 or 19
- perf-tool for benchmarking, debian package name: `linux-perf`

### General
- Install opam dependencies: `cd src/` `opam pin add -y .` `opam install --deps-only secwasm`
- Run the project with the Makefile in `src/`

### Development dependencies
- Ocaml formatting tool: `opam pin add ocamlformat 0.26.0` `opam install ocamlformat`
- Pre-commit hook to ensure formatting: `pip install pre-commit` then in the root repo: `pre-commit install`

## Running the tool
- See the Makefile for examples:
- `make test` to run the testsuite
- `make coverage` to generate a report of the test coverage
- `make run` to run the static typecheck on an example module
- `make bubblesort-benchmark` for benchmarking the performance penalty of the dynamic checks
- `make seqmem-benchmark` for benchmarking the performance penalty of the dynamic checks
