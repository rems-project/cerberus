# BMC notes

BMC is called in src/main. There are a bunch of commandline options
(`./cerberus --help`), the most basic are:

* `--bmc` to enable BMC
* `--bmc_conc` to enable the concurrency mode (flag doesn't work as they should yet in Bmc3)

There are two versions: the more complete version in `src/bmc.ml` from the
summer, and the WIP version `src/bmc3.ml` which is lacking features and is
slower for some reason. Currently, versions are just selected by
commenting/uncommenting out the relevant line in `src/main.ml`.


# Files

- `src/bmc.ml` and `src/bmc3.ml`: old and WIP BMC main file respectively. `bmc`
  is the main function
- `src/bmc_conc.ml`: `extract_executions` is where the graphs are output and
  currently where the concurrency memory model is selected (by
  commenting/uncommenting code; search `BmcMem`)
