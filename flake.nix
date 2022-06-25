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
    in {
      devShells = perSystem (system: {
        default = import ./shell.nix { pkgs = nixpkgsFor system; };
      });
    };
}
