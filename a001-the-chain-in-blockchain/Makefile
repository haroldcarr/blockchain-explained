#
# Created       : 2017 Jun 11 (Sun) 11:51:22 by Harold Carr.
# Last Modified : 2017 Jun 11 (Sun) 11:51:56 by Harold Carr.
#

G        = .generated

all :    md

md:
	cd src; pandoc Chain.lhs \
                       -o ../$(G)/Chain.md \
                       -s

clean :
	stack clean --full
	rm $(G)/*

# End of file.
