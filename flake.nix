{
  description = "Plutarch 2.0";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=nixos-unstable";
  };
  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      perSystem = nixpkgs.lib.genAttrs supportedSystems;
      nixpkgsFor = system: nixpkgs.legacyPackages.${system};
      haskellPackagesFor = system: (nixpkgsFor system).haskell.packages.ghc923;
    in
    {
      checks = perSystem (system: {
        formatting = (nixpkgsFor system).runCommandNoCC "formatting-check" {} ''
          cd ${self}
          ./bin/format check
          touch $out
        '';
        cabal2nix = (nixpkgsFor system).runCommandNoCC "cabal2nix-check" {
          nativeBuildInputs = [ (nixpkgsFor system).cabal2nix ];
        } ''
          cd ${self}
          diff <(cabal2nix ./.) plutarch-core.nix
          touch $out
        '';
      });
      apps = perSystem (system: {
        regen.type = "app";
        regen.program = builtins.toString ((nixpkgsFor system).writeShellScript "regen" ''
          cabal2nix ./. > plutarch-core.nix
          ./bin/format
        '');
      });
      packages = perSystem (system: {
        default = (haskellPackagesFor system).callPackage ./plutarch-core.nix {};
      });
      devShells = perSystem (system: {
        default = import ./shell.nix { pkgs = nixpkgsFor system; };
      });
    };
}
