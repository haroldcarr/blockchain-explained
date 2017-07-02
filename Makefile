#
# Created       : 2017 Jun 11 (Sun) 11:51:22 by Harold Carr.
# Last Modified : 2017 Jun 11 (Sun) 11:51:56 by Harold Carr.
#

G        = .generated

all :    md

md:
	echo `pwd`
	pandoc src/$(THE_FILE).lhs \
         -o $(G)/$(THE_FILE).md \
         -s

clean :
	stack clean --full
	rm $(G)/*

# End of file.
