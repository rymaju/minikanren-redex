# minikanren-redex

An attempt to get a redex for Minikanren!

More documentation and some code cleanup coming soon.

### Old Versions

An archive of how I got to the current version.

v1-v2 are based of the semantics.pdf document
v3 onwards was an approach based off of translating an actual minikanren implementation.

By v4, append, append-map, and delays are introduced using a "bucket" strategy (at this time I failed to use cons and tried to use built-in redex lists... bad idea.)

By v6 I had moved to cons-inf

By v7 I had delays working with this setup

By v8, relations calls (sort of)

By v9, fresh (sort of)

v10, the current version, fixes unification

There is still a known issue with nonterministic evaluation when there are multiple appends. This should be address by fiddling with `E` to make the evaluation context more precise (outermost leftmost append node first).
