{ pkgs ? import <nixpkgs> { } }:
with pkgs;
haskell.packages.ghc923.shellFor {
  packages = p: [
    (p.callPackage ./plutarch-core.nix { })
  ];
  buildHoogle = false;
  nativeBuildInputs = [
    cabal-install
    hlint
    cabal2nix
    nixpkgs-fmt
    curl
    haskellPackages.cabal-fmt
    haskell.packages.ghc923.fourmolu_0_7_0_1
  ];
}
