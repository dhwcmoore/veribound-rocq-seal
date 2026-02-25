(lang dune 3.0)

(package
 (name veribound-core)
 (license MIT)
 (authors "Duston Moore")
 (maintainers "dhwcmoore@gmail.com")
 (source (github dhwcmoore/veribound-rocq-seal))
 (homepage "https://github.com/dhwcmoore/veribound-rocq-seal")
 (documentation "https://github.com/dhwcmoore/veribound-rocq-seal")
 (depends ocaml dune yojson unix digestif str))
