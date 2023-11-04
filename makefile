
all:
	/home/students/inf/PUBLIC/MRJP/bin/bnfc -m -o AFLMay AFLMay.cf
	make -C AFLMay
	ghc -i.:AFLMay interpreter.hs -o interpreter 
	
clean:
	rm -f *.o *.hi interpreter
	