records-prototype
=================

A prototype implementation of overloaded record fields for GHC

http://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/Plan

Three versions are given, of gradually increasing complexity:

* [TrivialRecords.hs](https://github.com/adamgundry/records-prototype/blob/master/TrivialRecords.hs) overloads field access only
* [SimpleRecords.hs](https://github.com/adamgundry/records-prototype/blob/master/SimpleRecords.hs) integrates fields with simple lenses
* [RecordsPrototype.hs](https://github.com/adamgundry/records-prototype/blob/master/RecordsPrototype.hs) integrates fields with type-changing lenses
