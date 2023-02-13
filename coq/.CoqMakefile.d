src/Atom.vo src/Atom.glob src/Atom.v.beautified src/Atom.required_vo: src/Atom.v src/Frontier.vo src/Ninfty.vo
src/Atom.vio: src/Atom.v src/Frontier.vio src/Ninfty.vio
src/Atom.vos src/Atom.vok src/Atom.required_vos: src/Atom.v src/Frontier.vos src/Ninfty.vos
src/Clause.vo src/Clause.glob src/Clause.v.beautified src/Clause.required_vo: src/Clause.v src/Atom.vo src/Frontier.vo src/Ninfty.vo src/Misc.vo
src/Clause.vio: src/Clause.v src/Atom.vio src/Frontier.vio src/Ninfty.vio src/Misc.vio
src/Clause.vos src/Clause.vok src/Clause.required_vos: src/Clause.v src/Atom.vos src/Frontier.vos src/Ninfty.vos src/Misc.vos
src/Forward.vo src/Forward.glob src/Forward.v.beautified src/Forward.required_vo: src/Forward.v src/Sets.vo src/Clause.vo src/Atom.vo src/Frontier.vo src/Vars.vo src/VarsImp.vo src/Misc.vo src/Ninfty.vo src/Geq.vo src/Model.vo
src/Forward.vio: src/Forward.v src/Sets.vio src/Clause.vio src/Atom.vio src/Frontier.vio src/Vars.vio src/VarsImp.vio src/Misc.vio src/Ninfty.vio src/Geq.vio src/Model.vio
src/Forward.vos src/Forward.vok src/Forward.required_vos: src/Forward.v src/Sets.vos src/Clause.vos src/Atom.vos src/Frontier.vos src/Vars.vos src/VarsImp.vos src/Misc.vos src/Ninfty.vos src/Geq.vos src/Model.vos
src/Frontier.vo src/Frontier.glob src/Frontier.v.beautified src/Frontier.required_vo: src/Frontier.v src/Misc.vo src/Sets.vo src/Ninfty.vo
src/Frontier.vio: src/Frontier.v src/Misc.vio src/Sets.vio src/Ninfty.vio
src/Frontier.vos src/Frontier.vok src/Frontier.required_vos: src/Frontier.v src/Misc.vos src/Sets.vos src/Ninfty.vos
src/Geq.vo src/Geq.glob src/Geq.v.beautified src/Geq.required_vo: src/Geq.v src/Frontier.vo src/Clause.vo src/Ninfty.vo src/Sets.vo src/Atom.vo src/Vars.vo src/Model.vo src/VarsImp.vo
src/Geq.vio: src/Geq.v src/Frontier.vio src/Clause.vio src/Ninfty.vio src/Sets.vio src/Atom.vio src/Vars.vio src/Model.vio src/VarsImp.vio
src/Geq.vos src/Geq.vok src/Geq.required_vos: src/Geq.v src/Frontier.vos src/Clause.vos src/Ninfty.vos src/Sets.vos src/Atom.vos src/Vars.vos src/Model.vos src/VarsImp.vos
src/Main.vo src/Main.glob src/Main.v.beautified src/Main.required_vo: src/Main.v src/Sets.vo src/Clause.vo src/Atom.vo src/Frontier.vo src/Vars.vo src/VarsImp.vo src/Misc.vo src/Forward.vo src/Geq.vo src/Model.vo src/Ninfty.vo
src/Main.vio: src/Main.v src/Sets.vio src/Clause.vio src/Atom.vio src/Frontier.vio src/Vars.vio src/VarsImp.vio src/Misc.vio src/Forward.vio src/Geq.vio src/Model.vio src/Ninfty.vio
src/Main.vos src/Main.vok src/Main.required_vos: src/Main.v src/Sets.vos src/Clause.vos src/Atom.vos src/Frontier.vos src/Vars.vos src/VarsImp.vos src/Misc.vos src/Forward.vos src/Geq.vos src/Model.vos src/Ninfty.vos
src/Misc.vo src/Misc.glob src/Misc.v.beautified src/Misc.required_vo: src/Misc.v 
src/Misc.vio: src/Misc.v 
src/Misc.vos src/Misc.vok src/Misc.required_vos: src/Misc.v 
src/Model.vo src/Model.glob src/Model.v.beautified src/Model.required_vo: src/Model.v src/Sets.vo src/Clause.vo src/Atom.vo src/Frontier.vo src/Vars.vo src/Misc.vo src/Ninfty.vo
src/Model.vio: src/Model.v src/Sets.vio src/Clause.vio src/Atom.vio src/Frontier.vio src/Vars.vio src/Misc.vio src/Ninfty.vio
src/Model.vos src/Model.vok src/Model.required_vos: src/Model.v src/Sets.vos src/Clause.vos src/Atom.vos src/Frontier.vos src/Vars.vos src/Misc.vos src/Ninfty.vos
src/Ninfty.vo src/Ninfty.glob src/Ninfty.v.beautified src/Ninfty.required_vo: src/Ninfty.v 
src/Ninfty.vio: src/Ninfty.v 
src/Ninfty.vos src/Ninfty.vok src/Ninfty.required_vos: src/Ninfty.v 
src/Sets.vo src/Sets.glob src/Sets.v.beautified src/Sets.required_vo: src/Sets.v src/Misc.vo
src/Sets.vio: src/Sets.v src/Misc.vio
src/Sets.vos src/Sets.vok src/Sets.required_vos: src/Sets.v src/Misc.vos
src/Vars.vo src/Vars.glob src/Vars.v.beautified src/Vars.required_vo: src/Vars.v src/Atom.vo src/Clause.vo src/Frontier.vo src/Ninfty.vo src/Misc.vo src/Sets.vo
src/Vars.vio: src/Vars.v src/Atom.vio src/Clause.vio src/Frontier.vio src/Ninfty.vio src/Misc.vio src/Sets.vio
src/Vars.vos src/Vars.vok src/Vars.required_vos: src/Vars.v src/Atom.vos src/Clause.vos src/Frontier.vos src/Ninfty.vos src/Misc.vos src/Sets.vos
src/VarsImp.vo src/VarsImp.glob src/VarsImp.v.beautified src/VarsImp.required_vo: src/VarsImp.v src/Clause.vo src/Atom.vo src/Frontier.vo src/Sets.vo src/Vars.vo src/Model.vo
src/VarsImp.vio: src/VarsImp.v src/Clause.vio src/Atom.vio src/Frontier.vio src/Sets.vio src/Vars.vio src/Model.vio
src/VarsImp.vos src/VarsImp.vok src/VarsImp.required_vos: src/VarsImp.v src/Clause.vos src/Atom.vos src/Frontier.vos src/Sets.vos src/Vars.vos src/Model.vos
