{ pkgs ? import <nixpkgs> { } }:
with pkgs;
haskell.packages.ghc923.shellFor {
  packages = p: [
    (p.callPackage ./plutarch-core.nix { })
  ];
  buildHoogle = false;
  buildInputs = [ cabal-install cabal2nix curl nixpkgs-fmt ];
}
