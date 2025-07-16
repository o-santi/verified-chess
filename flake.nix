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
        coq_8_20
        (texlive.combine {
          inherit (texlive) scheme-basic collection-fontsrecommended
            dvisvgm dvipng # for preview and export as html
            biblatex latexmk babel-portuges
            abntex2 memoir xpatch booktabs textcase enumitem supertabular listings
            lastpage glossaries
            wrapfig amsmath ulem hyperref capt-of;
        })
        
      ];
    };
  };
}
