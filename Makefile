
AGDA := agda

test :
	$(AGDA) Everything.agda

html :
	rm -r -f /tmp/html
	$(AGDA) --html --html-dir=/tmp/html README.lagda.md

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f Lecture/ReasoningAboutPrograms/*.hs
