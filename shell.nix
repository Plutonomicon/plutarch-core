{ pkgs ? import <nixpkgs> {} }:
with pkgs;
let
  #mkDerivation = p: old: arg: old (arg // {libraryHaskellDepends = arg.libraryHaskellDepends ++ arg.testHaskellDepends;});
in haskell.packages.ghc922.shellFor {
  packages = p: [
    (p.callPackage ./plutarch-core.nix {})
  ];
  buildHoogle = false;
  buildInputs = [ cabal-install cabal2nix curl ];
}
