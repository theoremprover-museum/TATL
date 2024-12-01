let pkgs = import <nixpkgs> {};
in
pkgs.mkShell {
  packages = with pkgs; [ ocaml ocamlPackages.findlib dune_3 ocamlPackages.menhir ocamlPackages.ocamlgraph ];
}
