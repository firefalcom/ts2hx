package tshx;

import tshx.Ast;
import haxe.macro.Expr;
using StringTools;

typedef HaxeModule = {
	types: Array<TypeDefinition>,
	toplevel: Array<Field>
}

class Converter {

	static var nullPos = { min:0, max:0, file:"" };
	static var tDynamic = TPath({ pack: [], name: "Dynamic", sub: null, params: [] });
	static var tInt = { pack: [], name: "Int", sub: null, params: [] };
	static var tString = { pack: [], name: "String", sub: null, params: [] };

	static var reservedFieldName = ['continue'];
	static var excludedTypeName = ['Math'];

	static var printPrivate = false;

	public var modules(default, null):Map<String, HaxeModule>;
	var currentModule:HaxeModule;

	public function new() {
		modules = new Map();
	}

	public function convert(module:TsModule, skipTopLevel:Bool) {
		convertDecl(DModule(module));

		for(name in modules.keys()) {
			if (modules[name].toplevel.length > 0) {
				if(skipTopLevel){
					modules[name].toplevel = [];
				} else {
					modules[name].types.push({
						pack: [],
						name: name.replace("/", "_") + "TopLevel",
						pos: nullPos,
						isExtern: true,
						kind: TDClass(),
						fields: modules[name].toplevel
					});
				}
			}
		}

		cleanupDuplicateName();
		alignFieldSignature();
		removeExcludedTypes();
		convertInterfaceWhichDerivedFromClass();
		createExterns();
	}

	function cleanupDuplicateName():Void{
		for(name in modules.keys()) {
			for(type in modules[name].types) {
				var parent_fields : Array<haxe.macro.Field> = [];
				var sc = null;
				switch(type.kind){
					case TDClass(superClass, _, _):
						sc = superClass;
						if(superClass != null){
							parent_fields = parent_fields.concat(getFields(superClass.name));
						}
					default:
				}

				var field_names = [for(f in parent_fields) f.name];

				while( field_names.remove('new') ){}

				var filtered_field = type.fields.filter(function (v){ return field_names.indexOf(v.name) == -1;});

				type.fields = filtered_field;
			}
		}
	}

	function alignFieldSignature(){
		for(name in modules.keys()) {
			for(type in modules[name].types) {
				var parent_fields : Array<haxe.macro.Field> = [];
				var interfaces = null;
				switch(type.kind){
					case TDClass(_, null,_):
						continue;
					case TDClass(_, _interfaces, _):
						interfaces = _interfaces.map(function(t) if(t.params == null || t.params.length== 0) return getTypeByName(t.name) else return null);
					default:
						continue;
				}

				for(f in type.fields){
					if(f.name == 'new') continue;

					var interface_signature = getInterfaceSignature(interfaces, f.name);

					if(interface_signature != null){
						f.kind = interface_signature;
					}
				}
			}
		}
	}

	function getInterfaceSignature(interfaces:Array<haxe.macro.TypeDefinition>, name:String):FieldType{
		for(_interface in interfaces){
			if(_interface == null || _interface.fields == null) continue;
			for(field in _interface.fields) {
				if(field.name == name) return field.kind;
			}
		}

		return null;
	}

	function removeExcludedTypes() {
		for(name in modules.keys()) {
			var module = modules[name];

			module.types = module.types.filter(function(item){
				return excludedTypeName.indexOf(item.name) == -1;
			});
		}
	}

	function createExterns() {
		for(name in modules.keys()) {
			for(type in modules[name].types){

				switch( type.kind ){
					case TDClass(_,_,_):
					default: continue;
				}
				var type_name = type.name;
				var extern_name = '$name.$type_name';
				var param = {expr: EConst(CString(extern_name)) ,pos: null};
				var meta_data : MetadataEntry = {name: ':native', pos: null, params: [param]};
				type.meta = [meta_data];
			}
		}
	}

	function convertInterfaceWhichDerivedFromClass() {
		for(name in modules.keys()) {
			for(type in modules[name].types){
				switch(type.kind){
					case TDClass(parent, interfaces, true):
						if(parent != null){
							if(!isInterface(parent.name))
							{
								parent = null;
								continue;
							}
						}

						if(interfaces != null){
							interfaces = interfaces.filter(function(a) return isInterface(a.name));
						}

						type.kind = TDClass(parent, interfaces, true);
					default: continue;
				}
			}
		}
	}

	function isInterface(name:String):Bool{
		var type = getTypeByName(name);
		if(type == null){
			return false;
		}
		return switch(type.kind){
			case TDClass(_,_,true): true;
			default: false;
		}
	}

	function getFields(name:String):Array<haxe.macro.Field>{

		var current_type = null;
		for(module_name in modules.keys()) {
			for(type in modules[module_name].types) {
				if(type.name == name){
					current_type = type;
					break;
				}
			}
		}

		if(current_type != null){

			var fields = current_type.fields.copy();

			switch(current_type.kind){
				case TDClass(superClass, _, _):
					if(superClass != null){
						fields = fields.concat(getFields(superClass.name));
					}
				default:

			}

			return fields;
		} else {
			return [];
		}
	}

	function convertDecl(d:TsDeclaration) {
		switch(d) {
			case DModule(m) | DExternalModule(m):
				convertModule(m);
			case DInterface(i):
				var name = capitalize(i.name);
				var td = getTypeByName(name);

				if(td == null){
					currentModule.types.push(convertInterface(i));
				} else {
					mergeInterface(i, td);
				}
			case DClass(c):
				var name = capitalize(c.name);
				var td = getTypeByName(name);

				if(td == null){
					currentModule.types.push(convertClass(c));
				} else {
					mergeClass(c, td);
				}
			case DEnum(en):
				currentModule.types.push(convertEnum(en));
			case DTypedef(t):
				// TODO
			case DFunction(sig):
				currentModule.toplevel.push({
					name: sig.name,
					access: [AStatic],
					pos: nullPos,
					kind: FFun(convertFunction(sig.callSignature)),
				});
			case DVariable(v):
				currentModule.toplevel.push({
					name: v.name,
					access: [AStatic],
					pos: nullPos,
					kind: FVar(v.type == null ? tDynamic : convertType(v.type))
				});
			case DExportDecl(d, _):
				convertDecl(d);
			case DImport(_) | DExport(_):
				// TODO: do we need these?
		}
	}

	function convertFields(fl:Array<TsTypeMember>, isInterface:Bool) {
		var fields = [];
		var fieldMap = new Map();
		for (mem in fl) {
			var field = convertMember(mem, isInterface);
			if (field != null) {
				if (fieldMap.exists(field.name)) {
					var field2 = fieldMap[field.name];
					var f = switch(field.kind) {
						case FFun(f):
							f;
						case _:
							// TODO: this probably means we have a member + static property with the same name
							continue;
					}
					f.expr = { expr: EBlock([]), pos: nullPos };
					field2.meta.push({name: ":overload", params: [{expr:EFunction(null, f), pos: nullPos}], pos: nullPos});
				} else {
					fields.push(field);
					fieldMap[field.name] = field;
				}
			}
		}
		return fields;
	}

	function convertModule(m:TsModule) {
		var name = capitalize(pathToString(m.path));
		if (!modules.exists(name)) {
			modules[name] = {
				types: [],
				toplevel: []
			}
		}
		var old = currentModule;
		currentModule = modules[name];
		for (decl in m.elements) {
			convertDecl(decl);
		}
	}

	function convertInterface(i:TsInterface) : TypeDefinition {
		var fields = convertFields(i.t, true);
		var parents = i.parents.map(convertTypeReference);
		var td = {
			pack: [],
			name: capitalize(i.name),
			pos: nullPos,
			meta: [],
			params: i.params.map(convertTypeParameter),
			isExtern: false,
			kind: TDClass(null, parents, true),
			fields: fields
		}
		return td;
	}

	function mergeInterface(i:TsInterface, typeDefinition:TypeDefinition) : Void {
		var fields = convertFields(i.t, true);
		var parent_interfaces = i.parents.map(convertTypeReference);

		switch(typeDefinition.kind){

			case TDClass(parent, existing_interfaces, is_interface):
				typeDefinition.fields = typeDefinition.fields.concat(fields);
				typeDefinition.kind = TDClass(parent, existing_interfaces.concat(parent_interfaces), is_interface);

			default:
				trace("Unsupported");
		}
	}

	function convertClass(c:TsClass) : TypeDefinition {
		var fields = convertFields(c.t, false);
		var interfaces = c.interfaces.map(convertTypeReference);

		var td = {
			pack: [],
			name: capitalize(c.name),
			pos: nullPos,
			meta: [],
			params: c.params.map(convertTypeParameter),
			isExtern: true,
			kind: TDClass(c.parentClass == null ? null : convertTypeReference(c.parentClass), interfaces),
			fields: fields
		}
		return td;
	}

	function mergeClass(c:TsClass, typeDefinition : TypeDefinition ) : Void{
		var fields = convertFields(c.t, false);
		var interfaces = c.interfaces.map(convertTypeReference);
		interfaces = [];
		var parent_class = c.parentClass == null ? null : convertTypeReference(c.parentClass);
		var kind = TDClass(parent_class, interfaces);

		typeDefinition.isExtern = true;

		switch(typeDefinition.kind){
			case TDAlias(interface_kind):
				switch(interface_kind){
					case TAnonymous(existing_fields):
						typeDefinition.fields = existing_fields.concat(fields);
						typeDefinition.kind = kind;

					case TExtend(parents, existing_fields):
						typeDefinition.fields = existing_fields.concat(fields);
						typeDefinition.kind = kind;

					default:
						trace("Unsupported type, unable to merge interface");
				}

			case TDClass(parent, existing_interfaces, _):
				if(parent != null && parent != parent_class){
					trace("Merging of class with different parents is not supported");
				}

				typeDefinition.fields = typeDefinition.fields.concat(fields);
				typeDefinition.kind = TDClass(parent_class, existing_interfaces.concat(interfaces), false);

			default:
				trace("Unsupported");
		}
	}

	function convertEnum(en:TsEnum) : TypeDefinition {
		var i = 0;
		var fields = en.constructors.map(function(ctor) {
			if (ctor.value != null) {
				// TODO: I guess exported enums should not have int values
				i = Std.parseInt(ctor.value);
			}
			return {
				name: convertPropertyName(ctor.name),
				kind: FVar(null, { expr: EConst(CInt("" +i++)), pos: nullPos }),
				doc: null,
				meta: [],
				access: [],
				pos: nullPos
			}
		});
		var td = {
			pack: [],
			name: capitalize(en.name),
			pos: nullPos,
			meta: [{name: ":enum", params: [], pos: nullPos}],
			params: [],
			isExtern: false,
			kind: TDAbstract(TPath(tInt)),
			fields: fields
		}
		return td;
	}

	function convertMember(mem:TsTypeMember, isInterface:Bool) {
		var meta : Array<Dynamic>= [];
		var o = switch(mem) {
			case TProperty(sig):
				var kind = FVar(sig.type == null ? tDynamic : convertType(sig.type));
				var access = [];
				if(sig.isStatic) access.push(AStatic);
				if(!sig.isPublic) {
					if(!printPrivate) return null;
					access.push(APrivate);
				} else if(!isInterface){
					access.push(APublic);
				}
				{ kind: kind, name: sig.name, opt: sig.optional, access: access };
			case TMethod(sig):
				switch (sig.name) {
					case TIdentifier("constructor"):
						sig.callSignature.type = TPredefined(TVoid);
						sig.name = TIdentifier("new");
					case TIdentifier(name):
						if(reservedFieldName.indexOf(name)!=-1){
							var param = {expr: EConst(CString(name)) ,pos: null};
							meta.push({name:":native", params: [param], pos: nullPos});
							sig.name = TIdentifier('_' + name);
						}
					default:
				}
				var access = [];
				if(sig.isStatic) access.push(AStatic);
				if(!sig.isPublic) {
					if(!printPrivate) return null;
					access.push(APrivate);
				} else if(!isInterface) {
					access.push(APublic);
				}
				var kind = FFun(convertFunction(sig.callSignature));
				{ kind: kind, name: sig.name, opt: sig.optional, access: access };
			case TCall(_) | TConstruct(_) | TIndex(_):
				return null;
		}
		if(o.opt){
			meta.push({name: ":optional", params: [], pos: nullPos});
		}
		return {
			name: convertPropertyName(o.name),
			kind: o.kind,
			doc: null,
			meta: meta,
			access: o.access,
			pos: nullPos
		}
	}

	function convertFunction(sig:TsCallSignature):Function
		return {
			args: sig.arguments.map(convertArgument),
			ret: sig.type == null ? tDynamic : convertType(sig.type),
			expr: null,
			params: sig.params.map(convertTypeParameter)
		};

	function convertArgument(arg:TsArgument):FunctionArg {
		return {
			name: convertArgumentName(arg.name),
			opt: arg.optional,
			type: arg.type == null ? tDynamic : convertType(arg.type),
			value: null
		}
	}

	function convertArgumentName(name:String):String{
		return switch(name){
			case 'dynamic': '_dynamic';
			default : name;
		}
	}

	function convertTypeParameter(tp:TsTypeParameter):TypeParamDecl {
		return {
			name: tp.name,
			constraints: tp.constraint == null ? [] : [convertType(tp.constraint)],
			params: []
		}
	}

	function convertType(t:TsType):ComplexType {
		return switch(t) {
			case TPredefined(t):
				TPath(switch(t) {
					case TAny: { name: "Dynamic", pack: [], params: [], sub: null };
					case TNumber: { name: "Float", pack: [], params: [], sub: null };
					case TBoolean: { name: "Bool", pack: [], params: [], sub: null };
					case TString: { name: "String", pack: [], params: [], sub: null };
					case TVoid: { name: "Void", pack: [], params: [], sub: null };
				});
			case TTypeReference(t):
				TPath(convertTypeReference(t));
			case TTypeQuery(_), TIntersection(_):
				// TODO
				tDynamic;
			case TRestArgument(t):
				TPath({ name: "Rest", pack: ["haxe", "extern"], params: [TPType(convertType(t))] });
			case TTypeLiteral(t):
				switch(t) {
					case TObject(o):
						var fields:Array<Field> = convertFields(o, false);
						TAnonymous(fields.filter(function(v) return v != null));
					case TArray(t):
						TPath({ name: "Array", pack: [], params: [TPType(convertType(t))], sub: null});
					case TFunction(f):
						var args = f.arguments.map(function(arg) {
							var t = arg.type == null ? tDynamic : convertType(arg.type);
							return arg.optional ? TOptional(t) : t;
						});
						TFunction(args, convertType(f.ret));
					case TConstructor(_):
						// TODO
						tDynamic;
				}
			case TUnion(t1, t2):
				TPath({ name: "EitherType", pack: ["haxe", "extern"], params:[TPType(convertType(t1)), TPType(convertType(t2))], sub: null});
			case TTuple(tl):
				// TODO check if all types in a tuple are the same
				// TODO make an abstract for typed tuples?
				TPath({ name: "Array", pack: [], params: [TPType(TPath({ name: "Dynamic", pack: [], params: [], sub: null }))], sub: null});
			case TValue(v):
				switch( v ) {
				case VNumber(_): TPath(tInt);
				case VString(_): TPath(tString);
				}
			case TKeyof(t):
				convertType(t);
		}
	}

	function convertTypeReference(tref:TsTypeReference) {
		var tPath = {
			name: capitalize(tref.path[tref.path.length - 1]),
			pack: tref.path.slice(0, -1),
			params: tref.params.map(function(t) return TPType(convertType(t))),
			sub: null
		};
		switch [tPath.name, tPath.pack, tPath.params] {
			case ["Null", [], []]:
				tPath.name = "Dynamic";
			case ["Object", [], _]:
				tPath.name = "Dynamic";
			case ["RegExp", [], _]:
				tPath.pack = ["js"];
			case ["Function", [], _]:
				tPath.pack = ["haxe"];
				tPath.name = "Constraints";
				tPath.sub = "Function";
			case _:
		}
		return tPath;
	}

	function convertPropertyName(pn:TsPropertyName) {
		return switch(pn) {
			case TIdentifier(s): s;
			case TStringLiteral(s): s;
			case TNumericLiteral(s): "_" + s;
		}
	}

	function getTypeByName(name:String):TypeDefinition{
		for(type in currentModule.types){
			if(type.name == name){
				return type;
			}
		}

		return null;
	}

	function pathToString(p:TsIdentifierPath) {
		return p.join(".");
	}

	static public function capitalize(s:String) {
		return s.charAt(0).toUpperCase() + s.substr(1);
	}
}
