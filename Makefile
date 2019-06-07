
AGDA := agda

test :
	$(AGDA) Everything.agda

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f Lecture/ReasoningAboutPrograms/*.hs
