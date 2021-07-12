{ pkgs ? import <nixpkgs> {} }:
with pkgs;
mkShell {
  buildInputs = [ coq coqPackages.hierarchy-builder ];
}
