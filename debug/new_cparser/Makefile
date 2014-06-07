# Looking for Lem
ifneq ($(wildcard $(PWD)/../lem-csem/lem),)
  LEMDIR=$(PWD)/../lem-csem
else ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  $(error could not find lem (please set the variable LEM_PATH))
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=$(LEMDIR)/lem -wl ign  -wl_rename warn -lib $(LEMLIB_DIR)


OCAML_BUILD_DIR=_ocaml_build

$(OCAML_BUILD_DIR):
	@mkdir $(OCAML_BUILD_DIR)
	@cp $(LEMDIR)/ocaml-lib/*.ml $(LEMDIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)



$(OCAML_BUILD_DIR)/cabs.ml: cabs.lem | $(OCAML_BUILD_DIR)
	OCAMLRUNPARAM="" lem -ocaml Cabs.lem -outdir $(OCAML_BUILD_DIR)

$(OCAML_BUILD_DIR)/cabs.cmo: $(OCAML_BUILD_DIR)/cabs.ml
	cd $(OCAML_BUILD_DIR); ocamlbuild cabs.cmo

parser: $(OCAML_BUILD_DIR)/cabs.cmo
	menhir --infer --ocamlc "ocamlc -I $(OCAML_BUILD_DIR)/_build" --strict --explain Parser.mly


desugar: $(OCAML_BUILD_DIR)/cabs.cmo $(OCAML_BUILD_DIR)/parser.cmo
