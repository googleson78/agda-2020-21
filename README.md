## Binds cheatsheet
### Top level
| action               | spacemacs   | vscode  |
|----------------------|-------------|---------|
| Reload and typecheck | SPC m l     | C-c C-l |
| Restart Agda         | SPC m x r   | C-c C-r |
| Compute expression   | SPC m n     | C-c C-n |

### In hole
| action                                             | spacemacs | vscode    |
|----------------------------------------------------|-----------|-----------|
| [Auto] (`agsy`)                                    | SPC m a   | C-c C-a   |
| Ask for goal, and context                          | SPC m ,   | C-c C-,   |
| Ask for goal, context, and expression in hole      | SPC m .   | C-c C-.   |
| Try to use given expr to fill hole ("give")        | SPC m SPC | C-c C-SPC |
| Introduce arguments                                | SPC m c   | C-c C-c   |
| Case split (asks for input or names in the hole)   | SPC m c   | C-c C-c   |
| Introduce [copattern] (don't enter a name)         | SPC m c   | C-c C-c   |
| Attempt to introduce "contructor"\* ("refine")     | SPC m r   | C-c C-r   |
| Try to use function in hole, adding holes for args | SPC m r   | C-c C-r   |


#### \* "contructor" here means a couple of things
  * literally a constructor for a type, whose types matches - if ambiguous, the refine won't succeed
  * a lambda with as many arguments as possible - this is actually technically a constructor, for the function type (`->`)
  * a record with the required fields for the current type, with holes for the field values
  * **!VERY USEFUL! - if you have a function name in the hole, if the return type matches the goal, the function will be introduced with holes for its arguments**

## Resources
Some git repos for agda courses:
* https://github.com/pigworker/CS410-17
* https://github.com/pigworker/CS410-18

Nice exercises and approach (imo), with the huge bonus of having recorded [video lectures](https://github.com/pigworker/CS410-17#lecture-videos-on-youtube).

[PLFA](https://plfa.github.io/) - A loose adaptation of the [popular Coq based book](https://softwarefoundations.cis.upenn.edu/) to Agda.

Good for a gentle introduction, and some exercises. Also for lambda calculus related things in Agda.

### [Installation instructions with spacemacs in Bulgarian](https://gist.github.com/googleson78/85ce1a8a5d1480c9eb44c5f112cd7ac7)

## `Agda` in a browser
You can get a set up emacs agda environment in your browser at this website:
https://agdapad.quasicoherent.io/

Additionally, if you send someone the link to the same session, you can work together.

[copattern]: https://agda.readthedocs.io/en/v2.6.1.3/language/copatterns.html
[Auto]: https://agda.readthedocs.io/en/v2.6.1.3/tools/auto.html
