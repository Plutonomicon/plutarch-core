{
  description = "Plutarch 2.0";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=nixos-unstable";
  };
  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      perSystem = nixpkgs.lib.genAttrs supportedSystems;
      pkgsFor = system: nixpkgs.legacyPackages.${system};
      hsOverlay = hsPkgs: hsPkgs.override {
        overrides = final: prev: {
          plutarch-core = final.callPackage ./plutarch-core.nix { };
        };
      };
      hsPkgsFor = system: hsOverlay (pkgsFor system).haskell.packages.ghc923;
    in
    {
      checks = perSystem (system: {
        formatting = (pkgsFor system).runCommandNoCC "formatting-check" { } ''
          cd ${self}
          ./bin/format check
          touch $out
        '';
        cabal2nix = (pkgsFor system).runCommandNoCC "cabal2nix-check"
          {
            nativeBuildInputs = [ (pkgsFor system).cabal2nix ];
          } ''
          cd ${self}
          diff <(cabal2nix ./.) plutarch-core.nix
          touch $out
        '';
      });
      apps = perSystem (system: {
        regen.type = "app";
        regen.program = builtins.toString ((pkgsFor system).writeShellScript "regen" ''
          set -xe
          export PATH="${(hsPkgsFor system).fourmolu_0_7_0_1}/bin:$PATH"
          ${(pkgsFor system).cabal2nix}/bin/cabal2nix ./. > plutarch-core.nix
          ./bin/format
        '');
      });
      packages = perSystem (system: {
        default = (hsPkgsFor system).plutarch-core;
      });
      devShells = perSystem (system: {
        default = (hsPkgsFor system).shellFor {
          packages = p: [ p.plutarch-core ];
          buildHoogle = true;
          nativeBuildInputs = with (pkgsFor system); [
            cabal-install
            hlint
            cabal2nix
            nixpkgs-fmt
            curl
            haskellPackages.cabal-fmt
            (hsPkgsFor system).fourmolu_0_7_0_1
          ];
        };
      });
      hydraJobs = {
        checks = { inherit (self.checks) x86_64-linux; };
        packages = { inherit (self.packages) x86_64-linux; };
        devShells = { inherit (self.devShells) x86_64-linux; };
        apps.x86_64-linux.regen = self.apps.x86_64-linux.regen.program;
      };
    };
}
