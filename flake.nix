{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: let
    system= "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
  in {
    packages.${system}.default = self.packages.x86_64-linux.hello;
    devShells.${system}.default = pkgs.mkShell {
      packages = with pkgs; [
        coq_8_16
      ];
    };
  };
}
