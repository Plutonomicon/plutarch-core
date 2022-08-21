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
      formattersFor = system: with (pkgsFor system); [
        nixpkgs-fmt
        haskellPackages.cabal-fmt
        (hsPkgsFor system).fourmolu_0_7_0_1
      ];
      regen = system: (pkgsFor system).writeShellApplication {
        name = "regen";
        runtimeInputs = [ (pkgsFor system).cabal2nix ] ++ formattersFor system;
        text = ''
          set -xe
          cabal2nix ./. > plutarch-core.nix
          ./bin/format
        '';
      };
    in
    {
      checks = perSystem (system: {
        formatting = (pkgsFor system).runCommandNoCC "formatting-check"
          {
            nativeBuildInputs = formattersFor system;
          } ''
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
        regen.program = "${regen system}/bin/regen";
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
            curl
          ] ++ formattersFor system;
        };
      });
      hydraJobs = {
        checks = { inherit (self.checks) x86_64-linux; };
        packages = { inherit (self.packages) x86_64-linux; };
        devShells = { inherit (self.devShells) x86_64-linux; };
        apps.x86_64-linux.regen = regen "x86_64-linux";
      };
      herculesCI.ciSystems = [ "x86_64-linux" ];
    };
}
