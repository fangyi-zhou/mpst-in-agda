typecheck:
	agda Everything.agda

clean:
	$(RM) $(wildcard *.agdai)
	$(RM) -r _build
.PHONY: typecheck
