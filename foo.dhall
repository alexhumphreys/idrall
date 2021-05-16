let Files =
{ home : Text
, privateKey : Text
, publicKey : Text
}

let mkFiles : Text -> Files =
  \(user : Text) ->
  { home = "/home/${user}"
  , privateKey = "/home/${user}/.ssh/id_rsa"
  , publicKey = "/home/${user}/.ssh/id_rsa.pub"
  } : Files

in
mkFiles "jill"
