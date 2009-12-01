###########################
## Package configuration ##
###########################

TARGET   = qcad
BTARGET  = $(TARGET).byte
OTARGET  = $(TARGET).native

#########################
## Tools configuration ##
#########################
OCAMLBUILD_BIN   = ocamlbuild
OCAMLBUILD_EXTRA = -no-hygiene -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -cflag "-dtypes" -tag debug -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

#########
# Rules #
#########

.PHONY: all clear opt byte clean

all: clear opt

clear:
	rm -f $(BTARGET) $(OTARGET)

opt: $(OTARGET)

byte: $(BTARGET)

byte-debug:
	$(OCAMLBUILD) -tag debug src/$(BTARGET)

clean:
	$(OCAMLBUILD) -clean

%.byte %.native:
	$(OCAMLBUILD) src/$@
