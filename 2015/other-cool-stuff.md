great repository of academic papers to read:
[papers-we-love](https://github.com/papers-we-love/papers-we-love)

stuff to look into: 
* [chaos monkey](https://github.com/Netflix/SimianArmy/wiki/Chaos-Monkey)
* [quick check](https://github.com/nick8325/quickcheck)
* [cbor](https://hackage.haskell.org/package/CBOR) - alternative to protobuf, it's haskell, so it's probably waayyy cooler

approach to schema evolution when data is persisted in a db:
* Export data from db to json.
* Apply patches from version diff.
* Potentially apply extra transformation.
* Import transformed json to db.
