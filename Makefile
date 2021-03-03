.PHONY: all
all: iteree

.PHONY: iteree
iteree:
	idris2 --build iteree.ipkg
	idris2 --install iteree.ipkg

.PHONY: example-json
example-json: iteree
	idris2 -p contrib -p iteree examples/json.idr -x main
