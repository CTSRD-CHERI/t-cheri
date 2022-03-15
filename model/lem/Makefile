# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR:=$(shell opam config var sail:share)
SAIL:=sail
endif

LEM = lem

LEM_SRCS = capabilities.lem cheri_axioms.lem
ISA_TARGETS = Capabilities.thy Cheri_axioms.thy
ISA_PATHS = $(addprefix ../isabelle/,$(ISA_TARGETS))

all: $(ISA_PATHS)

$(ISA_PATHS) &: $(LEM_SRCS)
	$(LEM) -isa -lib Sail=$(SAIL_DIR)/src/gen_lib -outdir ../isabelle $^
