{ sources ? import nix/sources.nix, pkgs ? import sources.nixpkgs {} }:

pkgs.mkShell {
  packages = with pkgs; [ ocaml ocamlPackages.findlib dune_3 ocamlPackages.menhir ocamlPackages.ocamlgraph ];
}
