var fs = require("fs");
var types = require("ast-types");
var esprima = require("./node_modules/recast/node_modules/esprima-fb");
var escodegen = require("escodegen");
var escope = require("escope");
var estraverse = require("estraverse");

var source = esprima.parse(fs.readFileSync("libjass.js", { encoding: "utf8" }), { attachComment: true });

var result = esprima.parse(
	'(function (define) {\n' +
	'	var global = this;\n' +
	'	define(["exports"], function (libjass) {\n' +
	'	});\n' +
	'})((typeof define !== "undefined") ? define : function (/* ujs:unreferenced */ names, body) {\n' +
	'	body((typeof module !== "undefined") ? module.exports : (this.libjass = Object.create(null)));\n' +
	'});'
);

result.body[0].expression.callee.body.body[1].expression.arguments[1].body.body = source.body;

var firstLicenseHeader = null;
types.visit(result, {
	visitNode: function (path) {
		var node = path.node;

		if (node.leadingComments && node.leadingComments.length > 0) {
			var commentsToRemove = [];
			node.leadingComments.forEach(function (leadingComment, index) {
				if (leadingComment.type === "Block" && leadingComment.value.indexOf("Copyright") !== -1) {
					if (firstLicenseHeader === null) {
						firstLicenseHeader = leadingComment;
					}
					commentsToRemove.unshift(index);
				}
				else if (leadingComment.type === "Line" && leadingComment.value.substr(0, "/<reference".length) === "/<reference") {
					commentsToRemove.unshift(index);
				}
				else if (leadingComment.type === "Block") {
					var lines = leadingComment.value.split("\n");
					leadingComment.value = [lines[0]].concat(lines.slice(1).map(function (line) { return "        " + line; })).join("\n");
				}
			});
			commentsToRemove.forEach(function (index) {
				node.leadingComments.splice(index, 1);
			});
		}

		node.trailingComments = [];

		this.traverse(path);
	}
});

var firstExtends = null;
var nodesToRemove;
do {
	nodesToRemove = [];

	types.visit(result, {
		visitVariableDeclaration: function (path) {
			var variableDeclaration = path.node;

			variableDeclaration.declarations.forEach(function (declaration) {
				if (declaration.id.type === esprima.Syntax.Identifier && declaration.id.name === "libjass") {
					if (variableDeclaration.declarations.length === 1) {
						nodesToRemove.push({ parent: path.parentPath.node.body, element: variableDeclaration });
					}
					else {
						nodesToRemove.push({ parent: variableDeclaration.declarations, element: variableDeclaration.declarations[0] });
					}
				}
				else if (declaration.id.type === esprima.Syntax.Identifier && declaration.id.name === "__extends") {
					if (firstExtends === null) {
						firstExtends = declaration;
					}

					declaration.init = declaration.init.right;

					if (variableDeclaration.declarations.length === 1) {
						nodesToRemove.push({ parent: path.parentPath.node.body, element: variableDeclaration });
					}
					else {
						nodesToRemove.push({ parent: variableDeclaration.declarations, element: variableDeclaration.declarations[0] });
					}
				}

				if (declaration.id.type === esprima.Syntax.Identifier && declaration.id.leadingComments && declaration.id.leadingComments.length > 0 && variableDeclaration.declarations.length === 1) {
					variableDeclaration.leadingComments = declaration.id.leadingComments;
					declaration.id.leadingComments = [];
				}
			});

			this.traverse(path);
		}
	});

	nodesToRemove.forEach(function (item) {
		item.parent.splice(item.parent.indexOf(item.element), 1);
	});
}
while (nodesToRemove.length > 0);

types.visit(result, {
	visitCallExpression: function (path) {
		var node = path.node;
		var callee = node.callee;

		if (callee.type === esprima.Syntax.FunctionExpression && callee.params.length === 1 && callee.params[0].type === esprima.Syntax.Identifier && callee.params[0].name === "libjass") {
			node.arguments = [];
			callee.params = [];
		}

		this.traverse(path);
	}
});

var findDeclaration = function (identifier, scope) {
	for (var i = 0; i < scope.references.length; i++) {
		var reference = scope.references[i];
		if (reference.identifier !== identifier) {
			continue;
		}

		if (reference.resolved) {
			return reference.resolved.defs[reference.resolved.defs.length - 1].name;
		}

		for (var currentScope = reference.from; currentScope; currentScope = currentScope.upper) {
			for (var i = 0; i < currentScope.variables.length; i++) {
				var variable = currentScope.variables[i];
				if (variable.name === reference.identifier.name && variable.defs.length > 0) {
					return variable.defs[variable.defs.length - 1].name;
				}
			}
		}

		return null;
	}

	for (var i = 0; i < scope.variableScope.variables.length; i++) {
		var variable = scope.variableScope.variables[i];
		for (var j = 0; j < variable.identifiers.length; j++) {
			if (variable.identifiers[j] === identifier) {
				return identifier;
			}
		}
	}

	return null;
};

var scopeManager = escope.analyze(result);

types.visit(result, {
	visitFunctionDeclaration: function (path) {
		var functionDeclaration = path.node;

		functionDeclaration.params.forEach(function (param) {
			if (param.type === esprima.Syntax.Identifier && param.name[0] === "_" && param.name !== "_super") {
				scopeManager.attach();

				estraverse.traverse(functionDeclaration, {
					enter: function (node) {
						var scope = scopeManager.acquire(node);
						if (!scope) {
							return;
						}

						scope.references.forEach(function (reference) {
							if (reference.identifier.name === param.name) {
								var declaration = findDeclaration(reference.identifier, scope);
								if (declaration === param) {
									reference.identifier.name = reference.identifier.name.substr(1);
								}
							}
						});
					},
					leave: function (node) {
						scopeManager.release(node);
					}
				});

				scopeManager.detach();

				param.name = param.name.substr(1);
			}
		});

		this.traverse(path);
	}
});

types.visit(result, {
	visitFunction: function (path) {
		var func = path.node;

		for (var i = func.params.length - 1; i >= 0; i--) {
			var param = func.params[i];
			var isUnused = true;

			scopeManager.attach();

			estraverse.traverse(func, {
				enter: function (node) {
					var scope = scopeManager.acquire(node);
					if (!scope) {
						return;
					}

					for (var i = 0; i < scope.references.length; i++) {
						var reference = scope.references[i];
						if (reference.identifier.name === param.name) {
							var declaration = findDeclaration(reference.identifier, scope);
							if (declaration === param) {
								isUnused = false;
								return estraverse.VisitorOption.Break;
							}
						}
					}
				},
				leave: function (node) {
					scopeManager.release(node);
				}
			});

			scopeManager.detach();

			if (isUnused) {
				func.params.length--;
			}
		}

		this.traverse(path);
	}
});

result.body[0].leadingComments = [firstLicenseHeader];
source.body.splice(1, 0, types.builders.variableDeclaration("var", [firstExtends]));

fs.writeFileSync("libjass.recast.js", escodegen.generate(result, { comment: true, format: { quotes: "double" } }), { encoding: "utf8" });
