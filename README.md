# PLC Project
 CS-3820 Programming Language Concept
Originally created by Professor Garrett Morris, completed by Xiaoyang Yu in December 2020.

General idea of this program: 
     1. Parse plain text into datatype Expr. Codes in Parser.hs
     2. Evlaute Expr with function eval0. Codes in Main.hs
     3. Print out evaluated results. Codes in Main.hs

Please load libraries in the following order:
	cabal run meta ./lib/prelude.meta ./lib/arith.meta ./lib/list.meta ./lib/bool.meta ./lib/define.meta ./lib/test.meta
