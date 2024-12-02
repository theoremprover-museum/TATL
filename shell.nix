{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  packages = with pkgs; [ ocaml ocamlPackages.findlib dune_3 ocamlPackages.menhir ocamlPackages.ocamlgraph ];
}
