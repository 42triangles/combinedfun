# combinedfun
A little `nom`-like parser combinator library which stays away from macros, while trying to achieve at least part of the expressiveness of `nom`

Welcome to this little library, the only limit is the sky. And deep recursion. And compile times. And type inference that fucks up. And sometimes, if you're "lucky": Major fuckups when it comes to lifetime inference, leaving you having to use the methods instead of operators, since, while the methods actually use the operators, actually work there. Don't ask me why. It's a mystery.
