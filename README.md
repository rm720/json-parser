# Verified JSON Parser in HOL4 (Work in Progress)

[![Project Status: WIP – Initial development is in progress, but there has not yet been a stable, usable release suitable for the public.](https://www.repostatus.org/badges/latest/wip.svg)](https://www.repostatus.org/#wip)

## 🚧 Project Status: Work in Progress 🚧

This project is currently under active development. The core functionality is not yet complete, and the verification process is ongoing. We welcome contributions, but please note that major changes may occur as the project evolves.

## Overview

This project aims to implement a formally verified JSON parser in HOL, designed to complement the existing `json_to_mlstring` function in the `jsonLangTheory` of CakeML. The parser is intended to be proven correct and used in my cryptography project for election verification.

## Features (Planned)

- [ ] Formally verified JSON parsing
- [ ] Inverse operation to `json_to_mlstring` in CakeML's `jsonLangTheory`
- [ ] Guaranteed correct reading of JSON file

## Prerequisites

- [CakeML](https://cakeml.org/) compiler and proof tools
- [HOL4](https://hol-theorem-prover.org/) theorem prover

## Installation

- Follow the steps outlined in [HOWTO.md](HOWTO.md) to set up the project.
