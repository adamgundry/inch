toy:
	ghc --make -o toy Main.lhs

good:
	ghc -o toy Main.lhs -Wall -fno-warn-missing-signatures -fno-warn-unused-matches -fno-warn-name-shadowing

.PHONY: toy