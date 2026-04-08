# Software Engineering 2 Final Project

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](LICENSE)
[![Repository](https://img.shields.io/badge/repo-CotroneDeCiechiDeidier-181717?logo=github)](https://github.com/SimoneDeidier/CotroneDeCiechiDeidier)
[![Last Commit](https://img.shields.io/github/last-commit/SimoneDeidier/CotroneDeCiechiDeidier)](https://github.com/SimoneDeidier/CotroneDeCiechiDeidier/commits/main)
[![Stars](https://img.shields.io/github/stars/SimoneDeidier/CotroneDeCiechiDeidier?style=social)](https://github.com/SimoneDeidier/CotroneDeCiechiDeidier)

Final deliverable for the **Software Engineering 2** course at **Politecnico di Milano**.

This repository collects the full documentation work produced by team **CotroneDeCiechiDeidier** for the design of **CKB (CodeKataBattle)**, including:

- RASD (Requirements Analysis and Specification Document)
- DD (Design Document)
- Alloy formal model and verification artifacts
- Sequence diagrams, component design material, UI mockups, and final slide deck

## Team

- Professor: **Elisabetta Di Nitto**
- Group: **CotroneDeCiechiDeidier**
- Members:
	- [Mariarosaria Cotrone](https://github.com/marycotrone)
	- [Samuele De Ciechi](https://github.com/Samdec01)
	- [Simone Deidier](https://github.com/SimoneDeidier)

## Project Scope

The project models a platform where:

- educators create and manage tournaments and battles,
- students register to tournaments/battles and form teams,
- collaboration invitations and notifications are handled,
- battle outcomes include automatic and manual evaluation,
- badges are defined and assigned according to tournament lifecycle rules.

These behaviors are documented through functional flows (sequence diagrams) and formally constrained through an Alloy model.

## Repository Contents

### 1) RASD

The `RASD/` folder contains requirements-oriented artifacts:

- `mockups/`: UI mockups for common, educator, and student views.
- `sequence-diagrams/`: scenario-level interaction flows (source `.txt` and exported `.png`) for both educator and student roles.
- `alloy/`: formal model `CotroneDeCiechiDeidier.als` plus generated world screenshots.

Key RASD outputs are also available in:

- `delivery-folder/RASD v1.pdf`
- `delivery-folder/RASD v1.1.pdf`

### 2) DD

The `DD/` folder contains design-oriented artifacts:

- `component-diagram/`: global component architecture (`.vpd` source + image export).
- `component-interfaces/`: interface models for educator/student components (`.mdj` sources + images).
- `integration-plan/`: phased integration visuals.
- `sequence-diagrams/`: detailed interaction flows (source `.txt` + image exports).
- `user-interface-design/`: educator/student UI navigation/design maps (draw.io XML sources + images).

Key DD output is available in:

- `delivery-folder/DD v1.pdf`

### 3) Delivery Material

- `delivery-folder/`: official PDF submissions.
- `slideshow/`: final presentation (`.pdf`) and editable source (`.key`).

## Quick Navigation

- Final PDFs:
	- [RASD v1.1](delivery-folder/RASD%20v1.1.pdf)
	- [DD v1](delivery-folder/DD%20v1.pdf)
- Formal model:
	- [Alloy model](RASD/alloy/CotroneDeCiechiDeidier.als)
- Main interaction diagrams:
	- [RASD educator sequence diagrams](RASD/sequence-diagrams/educator)
	- [RASD student sequence diagrams](RASD/sequence-diagrams/student)
	- [DD educator sequence diagrams](DD/sequence-diagrams/educator)
	- [DD student sequence diagrams](DD/sequence-diagrams/student)

## How to Browse Artifacts

For a smooth review, this is a recommended reading order:

1. [RASD v1.1](delivery-folder/RASD%20v1.1.pdf) to understand goals, requirements, and main scenarios.
2. [Alloy model](RASD/alloy/CotroneDeCiechiDeidier.als) plus [Alloy images](RASD/alloy/images) to inspect formal constraints and validation worlds.
3. [DD v1](delivery-folder/DD%20v1.pdf) to move from requirements to architecture and design choices.
4. [DD component diagram](DD/component-diagram/component-diagram.jpg) and [DD component interfaces](DD/component-interfaces) for structural details.
5. [DD sequence diagrams](DD/sequence-diagrams) for role-specific interaction flows.
6. [Final slideshow](slideshow/CotroneDeCiechiDeidier.pdf) for a concise end-to-end project overview.

## Repository Structure

```text
.
|- DD/
|  |- component-diagram/
|  |- component-interfaces/
|  |- integration-plan/
|  |- sequence-diagrams/
|  `- user-interface-design/
|- RASD/
|  |- alloy/
|  |- mockups/
|  `- sequence-diagrams/
|- delivery-folder/
|- slideshow/
|- LICENSE
`- README.md
```

## Notes

- This repository is documentation-centric and does not include an executable software implementation.
- Many assets are provided both as editable sources (`.txt`, `.mdj`, `.vpd`, `.key`) and exported images/PDFs.

## License

Distributed under the [GNU General Public License v3.0](LICENSE).
