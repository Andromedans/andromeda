This directory contains rudimentary tests for Andromeda.

For each test `xyz` there is a `.m31` file with the test code and a
corresponding `.m31.ref` file with the reference output. A test succeeds if the
reference utput is identical to the actual output.

The tests in `./obsolete` subdirectory are obsolete and will be ignored by the
testing scripts. They are there so that a good soul will port the relevant ones
to the new Andromeda.

The tests are perfomed by the `./test.sh` script, which you can run as:

    ./test.sh [-v] [tests]

where `-v` means that the user should be asked to validate a test which fails
(this is used when things change). If not tests are given, then all of them are
run. To restrict testing to specific tests, provide a list of the relevant
`*.m31` files.
