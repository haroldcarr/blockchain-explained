#
# Created       : 2017 Jun 11 (Sun) 11:51:22 by Harold Carr.
# Last Modified : 2017 Jun 22 (Thu) 14:27:28 by Harold Carr.
#

G        = .generated

all :    md

md:
	cd src; pandoc Block.lhs \
                       -o ../$(G)/Block.md \
                       -s

clean :
	stack clean --full
	rm $(G)/*

# End of file.
