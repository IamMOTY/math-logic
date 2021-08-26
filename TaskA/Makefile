SOURCES=Main.hs 
GEN_SOURCES=Lexer.x Parser.y
GENERATED=Lexer.hs Parser.hs

.PHONY: pack all run 

all: parser

run: parser
	./parser

parser: $(GENERATED) $(SOURCES)
	ghc  -O2 Main.hs -o parser

$(GENERATED): $(GEN_SOURCES) $(SOURCES)
	alex Lexer.x 
	happy Parser.y

