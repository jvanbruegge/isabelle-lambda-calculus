OTT_FILES = ott/grammar.ott ott/typing.ott ott/small_step.ott

generate: $(OTT_FILES)
	#@eval $$(opam env) && ott -o Defs.thy $(OTT_FILES)
	@ott -o Defs.thy $(OTT_FILES)

watch:
	make generate
	@while true; do \
		inotifywait -e modify $(OTT_FILES) ; \
		make generate ; \
	 done
