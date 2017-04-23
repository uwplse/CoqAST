This plugin is a tutorial on how to traverse the Gallina AST. It is based heavily on template-coq, except with all of the performance boosts and extra functionality
stripped away to show a simpler example. __You should fork this plugin and play with it.__

The plugin itself is a work in progress. __Please submit a pull request if any of the comments
or code are incorrect or misleading.__

# Plugin functionality

The point of the plugin is not the functionality itself, but it still helps
to understand what it's doing before you make your own changes.

The plugin works roughly like Print, except that instead of pretty-printing a term,
it prints an s-expression that represents the AST.

For example:

    Coq < PrintAST nat.
    (Ind ((Name nat) (inductive_body (O 1 (Name nat)) (S 2 (Prod (Anonymous) (Name nat) (Name nat))))))

## Using the Plugin

The plugin is built to work with Coq 8.5pl3. It may not build for other versions of Coq, since the
AST sometimes changes between Coq versions.

To build:

        cd plugin
        make

This should install it in your Coq directory. In CoqTop (or whichever IDE you use):

      Coq < Require Import PrintAST.ASTPlugin.
      [Loading ML file ast_plugin.cmxs ... done]

To print:

        Coq < PrintAST le.
        (Ind ((Name le) (inductive_body (le_n 1 (Prod (Name n) (Name nat) (App (Name le) (Name n) (Name n)))) (le_S 2 (Prod (Name n) (Name nat) (Prod (Name m) (Name nat) (Prod (Anonymous) (App (Name le) (Name n) (Name m)) (App (Name le) (Name n) (App (Construct (Name nat) 2) (Name m))))))))))

### Toggling DeBruijn Indexing

You can change the plugin to use DeBruijn indexing instead of names:

    Coq < Set PrintAST Indexing.
    
    Coq < PrintAST nat.
    (Ind ((Name nat) (inductive_body (O 1 (Rel 1)) (S 2 (Prod (Anonymous) (Rel 1) (Rel 2))))))

### Showing Universe Instances

For universe-polymorphic constants, you can turn on printing universe instances:

    Coq < Set PrintAST Show Universes.

### Controlling the Printing Depth

You can change the depth at which the plugin prints definitions:

    Coq < PrintAST le with depth 1.
    (Ind ((Name le) (inductive_body (le_n 1 (Prod (Name n) (Ind ((Name nat) (inductive_body (O 1 (Rel 1)) (S 2 (Prod (Anonymous) (Rel 1) (Rel 2)))))) (App (Rel 2) (Rel 1) (Rel 1)))) (le_S 2 (Prod (Name n) (Ind ((Name nat) (inductive_body (O 1 (Rel 1)) (S 2 (Prod (Anonymous) (Rel 1) (Rel 2)))))) (Prod (Name m) (Ind ((Name nat) (inductive_body (O 1 (Rel 1)) (S 2 (Prod (Anonymous) (Rel 1) (Rel 2)))))) (Prod (Anonymous) (App (Rel 3) (Rel 2) (Rel 1)) (App (Rel 4) (Rel 3) (App (Construct (Ind ((Name nat) (inductive_body (O 1 (Rel 1)) (S 2 (Prod (Anonymous) (Rel 1) (Rel 2)))))) 2) (Rel 2))))))))))

The default depth is 0. If the argument is a constant or inductive type, the plugin always unfolds it.

# The Fun Part

Once you have a basic understanding of what this does, you can actually modify the plugin.

The only file you care about is `ast_plugin.ml4`. So open that up. It is extensively commented
to help guide you through changes.

After making your changes, build and load up CoqTop. Import the plugin again and call your command.
You should see the impact of your changes immediately.

## Modifying the Command

To modify the top-level behavior, change the `VERNAC COMMAND EXTEND` block of code at the end of the file.

## Changing or Adding Options

To modify the options, change the options code at the beginning of the file.

## Traversing the AST

To modify the behavior when traversing the AST, modify `build_ast` and the functions it calls.
This is the bulk of the code.

There are comments explaining the different terms in the functions that `build_ast` calls.
The file purposely has non-standard OCaml style to try to make it clear what's going on.

If it's still not clear what is going on from the comments, the code you care about in Coq itself is inside of
the `kernel` directory. Start with `term.mli` and open up associated files as you need them.
**If you do this, please submit a pull request with your discoveries.** My eventual goal is to make this
so clear that nobody even needs to open up `term.mli` to begin with, because digging through
legacy Coq code can be arduous.
