# *SAT 1.3 platform for experimenting with SAT-based procedures
# Copyright (C) 1999 Armando Tacchella
#
#     This program is free software; you can redistribute it and/or modify
#     it under the terms of the GNU General Public License as published by
#     the Free Software Foundation; either version 2 of the License, or
#     (at your option) any later version.
#
#     This program is distributed in the hope that it will be useful,
#     but WITHOUT ANY WARRANTY; without even the implied warranty of
#     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#     GNU General Public License for more details.
#
#     You should have received a copy of the GNU General Public License
#     along with this program; if not, write to the Free Software
#     Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
#
#     For problems and questions about *SAT contact:
#
#     Armando Tacchella
#     MRG-DIST University of Genova
#     V.le Causa 13
#     16142 GENOVA (ITALY)
#     tac@mrg.dist.unige.it

# ---------------------------------------------------------------------------
# GLOBAL SETTINGS (Do not change this!)
# ---------------------------------------------------------------------------
SHELL = /bin/sh

# ---------------------------------------------------------------------------
# C SETTINGS (Do not change this!)
# ---------------------------------------------------------------------------
CC = gcc
BASE_CFLAGS =  -O2 -pedantic -I../include -L../lib
#BASE_CFLAGS =  -g3 -Wall -pedantic -I../include -L../lib
LIB = -lfl -lglu -lm

# ---------------------------------------------------------------------------
# LEXER & PARSER (Do not change this!)
# ---------------------------------------------------------------------------
YACC = bison
YFLAGS = -d -y
LEX = flex

# ---------------------------------------------------------------------------
# INPUT SYNTAX (comment in/out PARSER, LEXER and SYNTAX at the same time!)
# ---------------------------------------------------------------------------

# Parser & Lexer for KsatLisp/KRIS syntax
PARSER = alc.y
LEXER = alc.lex
SYNTAX = -DNARY

# Parser & Lexer for KsatC syntax
#PARSER = c.y
#LEXER = c.lex
#SYNTAX = -DNARY

# Parser & Lexer for LWB syntax
#PARSER = lwb.y
#LEXER = lwb.lex
#SYNTAX = -DBARY

# Parser & Lexer for TPTP syntax
#PARSER = tptp.y
#LEXER = tptp.lex
#SYNTAX = -DBARY -DPURGE_COMMENTS

# ---------------------------------------------------------------------------
# DIRECTIVES (choose only one value for CFLAGS)
# ---------------------------------------------------------------------------

# RGFK - Random generated formulae (including Tableaux 99/2000 formulae)
CFLAGS =  -DOPTIMIZE -DTRIE_UNREV $(BASE_CFLAGS)

# HGFK - Hand generated formulae (Tableaux 98 formulae)
#CFLAGS = -DSORT_CLAUSES -DOPTIMIZE $(BASE_CFLAGS)

# Bare bones
#CFLAGS = $(BASE_CFLAGS)

# ---------------------------------------------------------------------------
# CODE ORGANIZATION (Do not change this!)
# ---------------------------------------------------------------------------

BASE_SRCS = fnode.c y.tab.c lex.yy.c dag.c monitor.c statistics.c dp_sat.c sato.c trie.c table.c set.c
BASE_OBJS = fnode.o y.tab.o lex.yy.o dag.o monitor.o statistics.o dp_sat.o sato.o trie.o table.o set.o

# ---------------------------------------------------------------------------
# TARGET EXECUTABLE (comment in/out SRCS, OBJS, LOGIC, EXEC at the same time)
# ---------------------------------------------------------------------------

#KSAT with DP (logic K)
SRCS = $(BASE_SRCS) kdp.c main-dp.c
OBJS = $(BASE_OBJS) kdp.o
LOGIC = -DKSAT 
EXEC = kSAT

# KPROVE with DP (logic K)
#SRCS = $(BASE_SRCS) kdp.c main-dp.c
#OBJS = $(BASE_OBJS) kdp.o
#LOGIC = -DKSAT -DNEGATE
#EXEC = kPROVE

# ESAT with DP (logic E)
#SRCS = $(BASE_SRCS) edp.c main-dp.c
#OBJS = $(BASE_OBJS) edp.o
#LOGIC = -DESAT 
#EXEC = eSAT

# ESAT with DP (logic E - translational approach)
#SRCS = $(BASE_SRCS) kdp.c main-dp.c
#OBJS = $(BASE_OBJS) kdp.o
#LOGIC = -DTRANSLATE_TO_K
#EXEC = ta4eSAT

# ===========================================================================
# NOTHING TO BE CHANGED BELOW THIS POINT!!!
# ===========================================================================

# ---------------------------------------------------------------------------
# RULES 
# ---------------------------------------------------------------------------

#The decision procedures
$(EXEC) : $(OBJS) main-dp.c
	$(CC) $(SYNTAX) $(MODIFIERS) $(LOGIC) $(CFLAGS) $(OBJS) main-dp.c $(LIB) -o $(EXEC)

y.tab.c : $(PARSER)
	$(YACC) $(YFLAGS) $(PARSER)
lex.yy.c: $(LEXER)
	$(LEX) $(LEXER)

# CLEAN FUNCTIONS
clean:
	rm -f *.tab.* *.yy.c *.o *~ *SAT *PROVE

# ---------------------------------------------------------------------------
# SETTING DEPENDENCIES (Do not change this!)
# ---------------------------------------------------------------------------
depend: y.tab.c lex.yy.c 
	makedepend -- $(CFLAGS) -- $(SRCS) --

# DO NOT DELETE THIS LINE -- make depend depends on it.

fnode.o: fnode.h /usr/include/malloc.h /usr/include/features.h
fnode.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
fnode.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
fnode.o: /usr/include/gnu/stubs.h /usr/include/stdio.h
fnode.o: /usr/include/bits/libc-header-start.h /usr/include/bits/types.h
fnode.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
fnode.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
fnode.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
fnode.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
fnode.o: ../include/util.h /usr/include/ctype.h /usr/include/endian.h
fnode.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
fnode.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
fnode.o: /usr/include/bits/types/locale_t.h
fnode.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
fnode.o: /usr/include/bits/math-vector.h
fnode.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
fnode.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
fnode.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
fnode.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
fnode.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
fnode.o: /usr/include/bits/fp-fast.h
fnode.o: /usr/include/bits/mathcalls-helper-functions.h
fnode.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
y.tab.o: fnode.h /usr/include/malloc.h /usr/include/features.h
y.tab.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
y.tab.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
y.tab.o: /usr/include/gnu/stubs.h /usr/include/stdio.h
y.tab.o: /usr/include/bits/libc-header-start.h /usr/include/bits/types.h
y.tab.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
y.tab.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
y.tab.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
y.tab.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
y.tab.o: ../include/util.h /usr/include/ctype.h /usr/include/endian.h
y.tab.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
y.tab.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
y.tab.o: /usr/include/bits/types/locale_t.h
y.tab.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
y.tab.o: /usr/include/bits/math-vector.h
y.tab.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
y.tab.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
y.tab.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
y.tab.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
y.tab.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
y.tab.o: /usr/include/bits/fp-fast.h
y.tab.o: /usr/include/bits/mathcalls-helper-functions.h
y.tab.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
lex.yy.o: /usr/include/stdio.h /usr/include/bits/libc-header-start.h
lex.yy.o: /usr/include/features.h /usr/include/stdc-predef.h
lex.yy.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
lex.yy.o: /usr/include/bits/long-double.h /usr/include/gnu/stubs.h
lex.yy.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
lex.yy.o: /usr/include/bits/types/__FILE.h /usr/include/bits/types/FILE.h
lex.yy.o: /usr/include/libio.h /usr/include/_G_config.h
lex.yy.o: /usr/include/bits/types/__mbstate_t.h /usr/include/bits/stdio_lim.h
lex.yy.o: /usr/include/bits/sys_errlist.h /usr/include/string.h
lex.yy.o: /usr/include/bits/types/locale_t.h
lex.yy.o: /usr/include/bits/types/__locale_t.h /usr/include/strings.h
lex.yy.o: /usr/include/errno.h /usr/include/bits/errno.h
lex.yy.o: /usr/include/linux/errno.h /usr/include/asm/errno.h
lex.yy.o: /usr/include/asm-generic/errno.h
lex.yy.o: /usr/include/asm-generic/errno-base.h /usr/include/stdlib.h
lex.yy.o: /usr/include/bits/waitflags.h /usr/include/bits/waitstatus.h
lex.yy.o: /usr/include/bits/floatn.h /usr/include/sys/types.h
lex.yy.o: /usr/include/bits/types/clock_t.h
lex.yy.o: /usr/include/bits/types/clockid_t.h
lex.yy.o: /usr/include/bits/types/time_t.h /usr/include/bits/types/timer_t.h
lex.yy.o: /usr/include/bits/stdint-intn.h /usr/include/endian.h
lex.yy.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
lex.yy.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
lex.yy.o: /usr/include/sys/select.h /usr/include/bits/select.h
lex.yy.o: /usr/include/bits/types/sigset_t.h
lex.yy.o: /usr/include/bits/types/__sigset_t.h
lex.yy.o: /usr/include/bits/types/struct_timeval.h
lex.yy.o: /usr/include/bits/types/struct_timespec.h
lex.yy.o: /usr/include/sys/sysmacros.h /usr/include/bits/sysmacros.h
lex.yy.o: /usr/include/bits/pthreadtypes.h
lex.yy.o: /usr/include/bits/thread-shared-types.h
lex.yy.o: /usr/include/bits/pthreadtypes-arch.h /usr/include/alloca.h
lex.yy.o: /usr/include/bits/stdlib-float.h fnode.h /usr/include/malloc.h
lex.yy.o: ../include/util.h /usr/include/ctype.h /usr/include/math.h
lex.yy.o: /usr/include/bits/math-vector.h
lex.yy.o: /usr/include/bits/libm-simd-decl-stubs.h
lex.yy.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
lex.yy.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
lex.yy.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
lex.yy.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
lex.yy.o: /usr/include/bits/fp-fast.h
lex.yy.o: /usr/include/bits/mathcalls-helper-functions.h
lex.yy.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
lex.yy.o: y.tab.h /usr/include/unistd.h /usr/include/bits/posix_opt.h
lex.yy.o: /usr/include/bits/environments.h /usr/include/bits/confname.h
lex.yy.o: /usr/include/bits/getopt_posix.h /usr/include/bits/getopt_core.h
dag.o: dag.h ../include/util.h /usr/include/stdio.h
dag.o: /usr/include/bits/libc-header-start.h /usr/include/features.h
dag.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
dag.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
dag.o: /usr/include/gnu/stubs.h /usr/include/bits/types.h
dag.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
dag.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
dag.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
dag.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
dag.o: /usr/include/ctype.h /usr/include/endian.h /usr/include/bits/endian.h
dag.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
dag.o: /usr/include/bits/uintn-identity.h /usr/include/bits/types/locale_t.h
dag.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
dag.o: /usr/include/bits/math-vector.h
dag.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
dag.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
dag.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
dag.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
dag.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
dag.o: /usr/include/bits/fp-fast.h
dag.o: /usr/include/bits/mathcalls-helper-functions.h
dag.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
dag.o: ../include/array.h ../include/list.h ../include/graph.h
dag.o: ../include/st.h fnode.h /usr/include/malloc.h addglu.h
monitor.o: monitor.h /usr/include/stdio.h
monitor.o: /usr/include/bits/libc-header-start.h /usr/include/features.h
monitor.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
monitor.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
monitor.o: /usr/include/gnu/stubs.h /usr/include/bits/types.h
monitor.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
monitor.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
monitor.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
monitor.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
monitor.o: /usr/include/malloc.h ../include/util.h /usr/include/ctype.h
monitor.o: /usr/include/endian.h /usr/include/bits/endian.h
monitor.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
monitor.o: /usr/include/bits/uintn-identity.h
monitor.o: /usr/include/bits/types/locale_t.h
monitor.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
monitor.o: /usr/include/bits/math-vector.h
monitor.o: /usr/include/bits/libm-simd-decl-stubs.h
monitor.o: /usr/include/bits/floatn.h /usr/include/bits/huge_val.h
monitor.o: /usr/include/bits/huge_val_flt128.h /usr/include/bits/huge_valf.h
monitor.o: /usr/include/bits/huge_vall.h /usr/include/bits/inf.h
monitor.o: /usr/include/bits/nan.h /usr/include/bits/flt-eval-method.h
monitor.o: /usr/include/bits/fp-logb.h /usr/include/bits/fp-fast.h
monitor.o: /usr/include/bits/mathcalls-helper-functions.h
monitor.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
statistics.o: statistics.h ../include/util.h /usr/include/stdio.h
statistics.o: /usr/include/bits/libc-header-start.h /usr/include/features.h
statistics.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
statistics.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
statistics.o: /usr/include/gnu/stubs.h /usr/include/bits/types.h
statistics.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
statistics.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
statistics.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
statistics.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
statistics.o: /usr/include/ctype.h /usr/include/endian.h
statistics.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
statistics.o: /usr/include/bits/byteswap-16.h
statistics.o: /usr/include/bits/uintn-identity.h
statistics.o: /usr/include/bits/types/locale_t.h
statistics.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
statistics.o: /usr/include/bits/math-vector.h
statistics.o: /usr/include/bits/libm-simd-decl-stubs.h
statistics.o: /usr/include/bits/floatn.h /usr/include/bits/huge_val.h
statistics.o: /usr/include/bits/huge_val_flt128.h
statistics.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
statistics.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
statistics.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
statistics.o: /usr/include/bits/fp-fast.h
statistics.o: /usr/include/bits/mathcalls-helper-functions.h
statistics.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
statistics.o: ../include/array.h ../include/list.h ../include/graph.h
statistics.o: ../include/var_set.h dag.h ../include/st.h fnode.h
statistics.o: /usr/include/malloc.h addglu.h common_sat.h
dp_sat.o: dp_sat.h ../include/util.h /usr/include/stdio.h
dp_sat.o: /usr/include/bits/libc-header-start.h /usr/include/features.h
dp_sat.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
dp_sat.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
dp_sat.o: /usr/include/gnu/stubs.h /usr/include/bits/types.h
dp_sat.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
dp_sat.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
dp_sat.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
dp_sat.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
dp_sat.o: /usr/include/ctype.h /usr/include/endian.h
dp_sat.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
dp_sat.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
dp_sat.o: /usr/include/bits/types/locale_t.h
dp_sat.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
dp_sat.o: /usr/include/bits/math-vector.h
dp_sat.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
dp_sat.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
dp_sat.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
dp_sat.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
dp_sat.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
dp_sat.o: /usr/include/bits/fp-fast.h
dp_sat.o: /usr/include/bits/mathcalls-helper-functions.h
dp_sat.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
dp_sat.o: ../include/array.h ../include/list.h ../include/graph.h
dp_sat.o: ../include/st.h dag.h fnode.h /usr/include/malloc.h addglu.h
dp_sat.o: common_sat.h satotrie.h monitor.h
sato.o: satotrie.h /usr/include/stdio.h /usr/include/bits/libc-header-start.h
sato.o: /usr/include/features.h /usr/include/stdc-predef.h
sato.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
sato.o: /usr/include/bits/long-double.h /usr/include/gnu/stubs.h
sato.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
sato.o: /usr/include/bits/types/__FILE.h /usr/include/bits/types/FILE.h
sato.o: /usr/include/libio.h /usr/include/_G_config.h
sato.o: /usr/include/bits/types/__mbstate_t.h /usr/include/bits/stdio_lim.h
sato.o: /usr/include/bits/sys_errlist.h dag.h ../include/util.h
sato.o: /usr/include/ctype.h /usr/include/endian.h /usr/include/bits/endian.h
sato.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
sato.o: /usr/include/bits/uintn-identity.h /usr/include/bits/types/locale_t.h
sato.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
sato.o: /usr/include/bits/math-vector.h
sato.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
sato.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
sato.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
sato.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
sato.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
sato.o: /usr/include/bits/fp-fast.h
sato.o: /usr/include/bits/mathcalls-helper-functions.h
sato.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
sato.o: ../include/array.h ../include/list.h ../include/graph.h
sato.o: ../include/st.h fnode.h /usr/include/malloc.h addglu.h common_sat.h
sato.o: monitor.h
trie.o: satotrie.h /usr/include/stdio.h /usr/include/bits/libc-header-start.h
trie.o: /usr/include/features.h /usr/include/stdc-predef.h
trie.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
trie.o: /usr/include/bits/long-double.h /usr/include/gnu/stubs.h
trie.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
trie.o: /usr/include/bits/types/__FILE.h /usr/include/bits/types/FILE.h
trie.o: /usr/include/libio.h /usr/include/_G_config.h
trie.o: /usr/include/bits/types/__mbstate_t.h /usr/include/bits/stdio_lim.h
trie.o: /usr/include/bits/sys_errlist.h dag.h ../include/util.h
trie.o: /usr/include/ctype.h /usr/include/endian.h /usr/include/bits/endian.h
trie.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
trie.o: /usr/include/bits/uintn-identity.h /usr/include/bits/types/locale_t.h
trie.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
trie.o: /usr/include/bits/math-vector.h
trie.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
trie.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
trie.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
trie.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
trie.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
trie.o: /usr/include/bits/fp-fast.h
trie.o: /usr/include/bits/mathcalls-helper-functions.h
trie.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
trie.o: ../include/array.h ../include/list.h ../include/graph.h
trie.o: ../include/st.h fnode.h /usr/include/malloc.h addglu.h common_sat.h
trie.o: monitor.h
table.o: table.h /usr/include/malloc.h /usr/include/features.h
table.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
table.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
table.o: /usr/include/gnu/stubs.h /usr/include/stdio.h
table.o: /usr/include/bits/libc-header-start.h /usr/include/bits/types.h
table.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
table.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
table.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
table.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
table.o: ../include/util.h /usr/include/ctype.h /usr/include/endian.h
table.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
table.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
table.o: /usr/include/bits/types/locale_t.h
table.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
table.o: /usr/include/bits/math-vector.h
table.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
table.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
table.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
table.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
table.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
table.o: /usr/include/bits/fp-fast.h
table.o: /usr/include/bits/mathcalls-helper-functions.h
table.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
table.o: ../include/sparse_int.h ../include/sparse.h
set.o: set.h /usr/include/limits.h /usr/include/bits/libc-header-start.h
set.o: /usr/include/features.h /usr/include/stdc-predef.h
set.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
set.o: /usr/include/bits/long-double.h /usr/include/gnu/stubs.h
set.o: /usr/include/bits/posix1_lim.h /usr/include/bits/local_lim.h
set.o: /usr/include/linux/limits.h /usr/include/bits/posix2_lim.h
set.o: /usr/include/math.h /usr/include/bits/types.h
set.o: /usr/include/bits/typesizes.h /usr/include/bits/math-vector.h
set.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
set.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
set.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
set.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
set.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
set.o: /usr/include/bits/fp-fast.h
set.o: /usr/include/bits/mathcalls-helper-functions.h
set.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
set.o: ../include/util.h /usr/include/stdio.h
set.o: /usr/include/bits/types/__FILE.h /usr/include/bits/types/FILE.h
set.o: /usr/include/libio.h /usr/include/_G_config.h
set.o: /usr/include/bits/types/__mbstate_t.h /usr/include/bits/stdio_lim.h
set.o: /usr/include/bits/sys_errlist.h /usr/include/ctype.h
set.o: /usr/include/endian.h /usr/include/bits/endian.h
set.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
set.o: /usr/include/bits/uintn-identity.h /usr/include/bits/types/locale_t.h
set.o: /usr/include/bits/types/__locale_t.h ../include/var_set.h
set.o: ../include/st.h dp_sat.h ../include/array.h ../include/list.h
set.o: ../include/graph.h dag.h fnode.h /usr/include/malloc.h addglu.h
set.o: common_sat.h satotrie.h monitor.h statistics.h
kdp.o: kdp.h dp_sat.h ../include/util.h /usr/include/stdio.h
kdp.o: /usr/include/bits/libc-header-start.h /usr/include/features.h
kdp.o: /usr/include/stdc-predef.h /usr/include/sys/cdefs.h
kdp.o: /usr/include/bits/wordsize.h /usr/include/bits/long-double.h
kdp.o: /usr/include/gnu/stubs.h /usr/include/bits/types.h
kdp.o: /usr/include/bits/typesizes.h /usr/include/bits/types/__FILE.h
kdp.o: /usr/include/bits/types/FILE.h /usr/include/libio.h
kdp.o: /usr/include/_G_config.h /usr/include/bits/types/__mbstate_t.h
kdp.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
kdp.o: /usr/include/ctype.h /usr/include/endian.h /usr/include/bits/endian.h
kdp.o: /usr/include/bits/byteswap.h /usr/include/bits/byteswap-16.h
kdp.o: /usr/include/bits/uintn-identity.h /usr/include/bits/types/locale_t.h
kdp.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
kdp.o: /usr/include/bits/math-vector.h
kdp.o: /usr/include/bits/libm-simd-decl-stubs.h /usr/include/bits/floatn.h
kdp.o: /usr/include/bits/huge_val.h /usr/include/bits/huge_val_flt128.h
kdp.o: /usr/include/bits/huge_valf.h /usr/include/bits/huge_vall.h
kdp.o: /usr/include/bits/inf.h /usr/include/bits/nan.h
kdp.o: /usr/include/bits/flt-eval-method.h /usr/include/bits/fp-logb.h
kdp.o: /usr/include/bits/fp-fast.h
kdp.o: /usr/include/bits/mathcalls-helper-functions.h
kdp.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
kdp.o: ../include/array.h ../include/list.h ../include/graph.h
kdp.o: ../include/st.h dag.h fnode.h /usr/include/malloc.h addglu.h
kdp.o: common_sat.h satotrie.h monitor.h set.h /usr/include/limits.h
kdp.o: /usr/include/bits/posix1_lim.h /usr/include/bits/local_lim.h
kdp.o: /usr/include/linux/limits.h /usr/include/bits/posix2_lim.h
kdp.o: ../include/var_set.h statistics.h
main-dp.o: /usr/include/stdio.h /usr/include/bits/libc-header-start.h
main-dp.o: /usr/include/features.h /usr/include/stdc-predef.h
main-dp.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
main-dp.o: /usr/include/bits/long-double.h /usr/include/gnu/stubs.h
main-dp.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
main-dp.o: /usr/include/bits/types/__FILE.h /usr/include/bits/types/FILE.h
main-dp.o: /usr/include/libio.h /usr/include/_G_config.h
main-dp.o: /usr/include/bits/types/__mbstate_t.h
main-dp.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
main-dp.o: /usr/include/sys/time.h /usr/include/bits/types/time_t.h
main-dp.o: /usr/include/bits/types/struct_timeval.h /usr/include/sys/select.h
main-dp.o: /usr/include/bits/select.h /usr/include/bits/types/sigset_t.h
main-dp.o: /usr/include/bits/types/__sigset_t.h
main-dp.o: /usr/include/bits/types/struct_timespec.h
main-dp.o: /usr/include/sys/resource.h /usr/include/bits/resource.h
main-dp.o: /usr/include/bits/types/struct_rusage.h /usr/include/signal.h
main-dp.o: /usr/include/bits/signum.h /usr/include/bits/signum-generic.h
main-dp.o: /usr/include/bits/types/sig_atomic_t.h
main-dp.o: /usr/include/bits/types/siginfo_t.h
main-dp.o: /usr/include/bits/types/sigval_t.h
main-dp.o: /usr/include/bits/siginfo-arch.h
main-dp.o: /usr/include/bits/siginfo-consts.h
main-dp.o: /usr/include/bits/types/sigevent_t.h
main-dp.o: /usr/include/bits/sigevent-consts.h /usr/include/bits/sigaction.h
main-dp.o: /usr/include/bits/sigcontext.h /usr/include/bits/types/stack_t.h
main-dp.o: /usr/include/sys/ucontext.h /usr/include/bits/sigstack.h
main-dp.o: /usr/include/bits/ss_flags.h
main-dp.o: /usr/include/bits/types/struct_sigstack.h
main-dp.o: /usr/include/bits/pthreadtypes.h
main-dp.o: /usr/include/bits/thread-shared-types.h
main-dp.o: /usr/include/bits/pthreadtypes-arch.h
main-dp.o: /usr/include/bits/sigthread.h fnode.h /usr/include/malloc.h
main-dp.o: ../include/util.h /usr/include/ctype.h /usr/include/endian.h
main-dp.o: /usr/include/bits/endian.h /usr/include/bits/byteswap.h
main-dp.o: /usr/include/bits/byteswap-16.h /usr/include/bits/uintn-identity.h
main-dp.o: /usr/include/bits/types/locale_t.h
main-dp.o: /usr/include/bits/types/__locale_t.h /usr/include/math.h
main-dp.o: /usr/include/bits/math-vector.h
main-dp.o: /usr/include/bits/libm-simd-decl-stubs.h
main-dp.o: /usr/include/bits/floatn.h /usr/include/bits/huge_val.h
main-dp.o: /usr/include/bits/huge_val_flt128.h /usr/include/bits/huge_valf.h
main-dp.o: /usr/include/bits/huge_vall.h /usr/include/bits/inf.h
main-dp.o: /usr/include/bits/nan.h /usr/include/bits/flt-eval-method.h
main-dp.o: /usr/include/bits/fp-logb.h /usr/include/bits/fp-fast.h
main-dp.o: /usr/include/bits/mathcalls-helper-functions.h
main-dp.o: /usr/include/bits/mathcalls.h /usr/include/bits/iscanonical.h
main-dp.o: dag.h ../include/array.h ../include/list.h ../include/graph.h
main-dp.o: ../include/st.h addglu.h dp_sat.h common_sat.h satotrie.h
main-dp.o: monitor.h statistics.h ../include/var_set.h table.h
main-dp.o: ../include/sparse_int.h ../include/sparse.h set.h
main-dp.o: /usr/include/limits.h /usr/include/bits/posix1_lim.h
main-dp.o: /usr/include/bits/local_lim.h /usr/include/linux/limits.h
main-dp.o: /usr/include/bits/posix2_lim.h
