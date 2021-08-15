let Inigo = { depends : List Text
, deps : List { name : Text, ns : Text, requirement : Text }
, description : Optional Text
, devDeps : List { name : Text, ns : Text, requirement : Text }
, executable : Optional Text
, gitDeps : List { commit : Text, subDirs : List Text, url : Text }
, license : Optional Text
, link : Optional Text
, localDeps : List Text
, main : Optional Text
, modules : List Text
, ns : Text
, package : Text
, readme : Optional Text
, sourcedir : Text
, version : Text
}

in
{ ns = "AlexHumphreys"
, package = "Idrall"
, version = "0.1.0"
, sourcedir = "."
, description = Some "Dhall compiler for Idris2"
, executable = None Text
, modules =
  [  "Idrall.Expr"
  ,  "Idrall.Value"
  ,  "Idrall.Resolve"
  ,  "Idrall.Parser"
  ,  "Idrall.Lexer"
  ,  "Idrall.Eval"
  ,  "Idrall.Check"
  ,  "Idrall.Error"
  ,  "Idrall.Map"
  ,  "Idrall.IOEither"
  ,  "Idrall.Path"
  ,  "Idrall.TestHelper"
  ,  "Idrall.APIv1"
  ,  "Idrall.API.V2"
  ,  "Idrall.Derive"
  ] : List Text
, readme = Some "./README.md"
, license = Some "MPL2"
, link = None Text
, main = None Text
, depends = ["base", "contrib"] : List Text
, deps = [] : (List ({ns : Text, name : Text, requirement : Text }))
, devDeps =  [] : List { ns : Text, name : Text, requirement : Text }
, localDeps = [] : List Text
, gitDeps = [] : List { url : Text, commit : Text, subDirs : List Text }
} : Inigo
