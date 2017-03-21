Plugin for printing semi-canonical Coq ASTs with kernel names (slow) and hashes of them (faster).

```coq
(* print list of identifier ASTs to stdout *)
AST List.map alternate.alternation.

(* print list of identifier ASTs to file *)
AST "asts.txt" List.map alternate.alternation.

(* print MD5 digests of identifiers as JSON to stdout *)
Digest MD5 List.map alternate.alternation.

(* print MD5 digests of identifiers as JSON to file digests.json *)
Digest MD5 "digests.json" List.map alternate.alternation.

(* print ASTs for all identifiers in modules/files List and Logic to file asts.txt *)
ModuleAST "asts.txt Logic List.

(* print MD5 digests for all identifiers in modules/files List and Logic to file digests.json *)
ModuleDigest MD5 "digests.json" Logic List.
```
