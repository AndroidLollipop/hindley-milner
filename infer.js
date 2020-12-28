var typeID = 0
const newVarID = () => typeID++
const newVar = () => ({
  type: "TypeVar",
  typeID: newVarID()
})
const newEnv = () => ({})
const clone = env => ({...env})
const Lam = (v, body) => ({
  type: "Lambda",
  v,
  body
})
const App = (f, x) => ({
  type: "Apply",
  f,
  x
})
const Let = (v, x, body) => ({
  type: "Let",
  v,
  x,
  body
})
const LetRec = (v, x, body) => ({
  type: "LetRec",
  v,
  x,
  body
})
const Var = v => ({
  type: "Var",
  v
})
const makeParametricType = (name, params) => ({
  type: "ParametricType",
  name,
  params
})
const Integer = makeParametricType("Integer", [])
const Bool = makeParametricType("Bool", [])
const makeFunctionType = (from, to) => makeParametricType("Function", [from, to])
const deepClone = (x, monomorphic) => {
  var mappings = {}
  const deepCloneRec = (x, monomorphic) => {
    x = resolve(x)
    if (x.type === "TypeVar") {
      if (monomorphic[x] !== true) {
        if (mappings[x] === undefined) {
          mappings[x] = newVar()
        }
        return mappings[x]
      }
      return x
    }
    if (typeof x === "object" || typeof x === "function") {
      var res = Array.isArray(x) ? [] : {}
      for (prop in x) {
        res[prop] = deepCloneRec(x[prop], monomorphic)
      }
      return res
    }
    else {
      return x
    }
  }
  return deepCloneRec(x, monomorphic)
}
const resolve = (node) => {
  return node.instance === undefined ? node : resolve(node.instance)
}
const analyse = (node, env, monomorphic=null) => {
  if (monomorphic === null) {
    monomorphic = {}
  }
  if (node.type === "Integer") {
    return Integer
  }
  if (node.type === "Var") {
    return deepClone(env[node.v], monomorphic)
  }
  if (node.type === "Apply") {
    const funType = analyse(node.f, env, monomorphic)
    const argType = analyse(node.x, env, monomorphic)
    const resType = newVar()
    unify(makeFunctionType(argType, resType), funType)
    return resType
  }
  if (node.type === "Lambda") {
    const argType = newVar()
    const newEnv = clone(env)
    newEnv[node.v] = argType
    const newMonomorphic = clone(monomorphic)
    newMonomorphic[argType] = true
    const resType = analyse(node.body, newEnv, newMonomorphic)
    return makeFunctionType(argType, resType)
  }
  if (node.type === "Let") {
    const xType = analyse(node.x, env, monomorphic)
    const newEnv = clone(env)
    newEnv[node.v] = xType
    return analyse(node.body, newEnv, monomorphic)
  }
  if (node.type === "LetRec") {
    const newType = newVar()
    const newEnv = clone(env)
    newEnv[node.v] = newType
    const newMonomorphic = clone(monomorphic)
    newMonomorphic[newType] = true
    const xType = analyse(node.x, newEnv, newMonomorphic)
    unify(newType, xType)
    return analyse(node.body, newEnv, monomorphic)
  }
  throw "EvalError: unknown node type"
}
const occursInType = (t, type) => {
  type = resolve(type)
  if (type === t) {
    return true
  }
  if (type.type === "ParametricType") {
    return occursInTypes(t, type.params)
  }
  return false
}
const occursInTypes = (t, types) => {
  for (type of types) {
    if (occursInType(t, type)) {
      return true
    }
  }
  return false
}
const unify = (t1, t2) => {
  t1 = resolve(t1)
  t2 = resolve(t2)
  if (t1.type === "TypeVar") {
    if (t1 != t2) {
      if (occursInType(t1, t2)) {
        throw "TypeError: recursive type"
      }
      t1.instance = t2
    }
  }
  else if (t1.type === "ParametricType" && t2.type === "TypeVar") {
    unify(t2, t1)
  }
  else if (t1.type === "ParametricType" && t2.type === "ParametricType") {
    if (t1.name !== t2.name || t1.params.length !== t2.params.length) {
      throw "TypeError: types do not match"
    }
    for (var i = 0; i < t1.params.length; i++) {
      unify(t1.params[i], t2.params[i])
    }
  }
  else {
    throw "TypeError: unification failed"
  }
}
const newBuiltinEnv = () => ({
  "increment": makeFunctionType(Integer, Integer),
  "add": makeFunctionType(Integer, makeFunctionType(Integer, Integer))
})
console.log(JSON.stringify(analyse(Lam("x", Lam("y", Var("x"))), newEnv())))
console.log(JSON.stringify(analyse(Lam("x", Let("x", Var("x"), Lam("y", Var("x"))), newEnv()))))
console.log(JSON.stringify(analyse(Lam("x", Let("x", Var("x"), Lam("y", App(App(Var("add"), Var("x")), Var("y"))))), newBuiltinEnv())))
