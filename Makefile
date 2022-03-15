all: lem tool

lem:
	$(MAKE) -C model/lem

tool:
	$(MAKE) -C tools
