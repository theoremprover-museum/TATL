# TATL*

This is the ATL* reasoner TATL*.

## Build
![CI](https://github.com/theoremprover-museum/TATL/actions/workflows/blank.yml/badge.svg)

Since TATL* is written in OCaml, we use the de facto standard build tool dune.
Building is done with `dune build` and to quickly execute you can run `dune exec tatl`.
Dune will complain about missing dependencies which you can install using `opam`.

For convenience, we provide a [nix shell](https://nixos.org/) with all dependencies present you can enter with `nix-shell` after setting up nix.

## License

The tool was develloped by Amèlie Regnault and open sourced under the Apache 2.0 license with permission.

## Development Status

The tool is considered stable and maintained by Merlin Humml, so feel free to open issues or PRs.
