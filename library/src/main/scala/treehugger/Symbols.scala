package treehugger

import Flags._
import api.Modifier

import java.util.concurrent.atomic.AtomicInteger

trait Symbols extends api.Symbols { self: Forest =>
  import definitions._

  private val ids = new AtomicInteger(0)

  abstract class Symbol(
      val rawowner: Symbol,
      val rawpos: Position,
      val rawname: Name,
      val rawflags: Long,
      val privateWithin: Symbol,
      val annotations: List[AnnotationInfo]
  ) extends AbsSymbol
      with HasFlags {

    type FlagsType          = Long
    type AccessBoundaryType = Symbol
    type AnnotationType     = AnnotationInfo

    val id = ids.getAndIncrement()

    def pos = rawpos

    override def hasModifier(mod: Modifier.Value) =
      hasFlag(flagOfModifier(mod)) &&
        (!(mod == Modifier.bynameParameter) || isTerm) &&
        (!(mod == Modifier.covariant) || isType)

    override def allModifiers: Set[Modifier.Value] =
      Modifier.values filter hasModifier

// ------ copy primitives (overridden in each concrete class) ----------------------

    protected def withRawflags(f: Long): Symbol
    protected def withPrivateWithin(pw: Symbol): Symbol
    protected def copyAnnotations(a: List[AnnotationInfo]): Symbol

// ------ creators -------------------------------------------------------------------

    final def newValue(pos: Position, name: TermName) =
      new TermSymbol(this, pos, name)
    final def newValue(name: TermName, pos: Position = NoPosition) =
      new TermSymbol(this, pos, name)
    final def newVariable(pos: Position, name: TermName) =
      newValue(pos, name).setFlag(MUTABLE)
    final def newValueParameter(pos: Position, name: TermName) =
      newValue(pos, name).setFlag(PARAM)

    /** Create local dummy for template (owner of local blocks) */
    final def newLocalDummy(pos: Position) =
      newValue(pos, nme.localDummyName(this))
    final def newMethod(pos: Position, name: TermName) =
      new MethodSymbol(this, pos, name).setFlag(METHOD)
    final def newMethod(name: TermName, pos: Position = NoPosition) =
      new MethodSymbol(this, pos, name).setFlag(METHOD)
    final def newLabel(pos: Position, name: TermName) =
      newMethod(pos, name).setFlag(LABEL)

    /**
     * Propagates ConstrFlags (JAVA, specifically) from owner to constructor.
     */
    final def newConstructor(pos: Position) =
      newMethod(pos, nme.CONSTRUCTOR) setFlag getFlag(ConstrFlags)

    /** Static constructor with info set. */
    def newStaticConstructor(pos: Position) =
      newConstructor(pos) setFlag STATIC

    /** Instance constructor with info set. */
    def newClassConstructor(pos: Position) =
      newConstructor(pos)

    private def finishModule(
        m: ModuleSymbol,
        clazz: ClassSymbol
    ): ModuleSymbol = {
      val extraFlags = if (isPackage) MODULE | FINAL else MODULE
      m.copy(rawflags = m.rawflags | extraFlags, referenced = clazz)
    }

    private def finishModule(m: ModuleSymbol): ModuleSymbol = {
      val extraFlags = if (isPackage) MODULE | FINAL else MODULE
      val mWithFlags = m.copy(rawflags = m.rawflags | extraFlags)
      mWithFlags.copy(referenced = new ModuleClassSymbol(mWithFlags))
    }

    final def newModule(
        pos: Position,
        name: TermName,
        clazz: ClassSymbol
    ): ModuleSymbol =
      finishModule(new ModuleSymbol(this, pos, name), clazz)

    final def newModule(
        name: TermName,
        clazz: Symbol,
        pos: Position = NoPosition
    ): ModuleSymbol =
      newModule(pos, name, clazz.asInstanceOf[ClassSymbol])

    final def newModule(pos: Position, name: TermName): ModuleSymbol =
      finishModule(new ModuleSymbol(this, pos, name))

    final def newModule(name: TermName): ModuleSymbol =
      finishModule(new ModuleSymbol(this, NoPosition, name))

    final def newPackage(pos: Position, name: TermName): ModuleSymbol = {
      val extraFlags  = if (isPackage) MODULE | FINAL else MODULE
      val moduleFlags = extraFlags | JAVA | PACKAGE
      val m           = new ModuleSymbol(this, pos, name, moduleFlags)
      val classFlags  = m.getFlag(ModuleToClassFlags) | MODULE | JAVA | PACKAGE
      val clazz       = new ModuleClassSymbol(this, pos, name.toTypeName, classFlags)
      m.copy(referenced = clazz)
    }
    final def newPackage(
        name: TermName,
        pos: Position = NoPosition
    ): ModuleSymbol =
      newPackage(pos, name)
    final def newModuleClass(pos: Position, name: Name, flags: Long = 0L) =
      new ModuleClassSymbol(this, pos, name.toTypeName, flags)
    final def newModuleClass(name: Name, pos: Position = NoPosition) =
      new ModuleClassSymbol(this, pos, name.toTypeName)

    final def newClass(pos: Position, name: Name) =
      new ClassSymbol(this, pos, name.toTypeName)
    final def newClass(name: Name, pos: Position = NoPosition) =
      new ClassSymbol(this, pos, name.toTypeName)

    /**
     * Refinement types P { val x: String; type T <: Number } also have
     * symbols, they are refinementClasses
     */
    final def newRefinementClass(pos: Position) =
      newClass(pos, tpnme.REFINE_CLASS_NAME)

    /**
     * Symbol of a type definition type T = ...
     */
    final def newAliasType(pos: Position, name: Name) =
      new TypeSymbol(this, pos, name.toTypeName)
    final def newAliasType(name: Name, pos: Position = NoPosition) =
      new TypeSymbol(this, pos, name.toTypeName)

    /**
     * Synthetic value parameters when parameter symbols are not available.
     * Calling this method multiple times will re-use the same parameter names.
     */
    final def newSyntheticValueParams(argtypes: List[Type]): List[Symbol] =
      newSyntheticValueParamss(List(argtypes)).head

    /**
     * Synthetic value parameter when parameter symbol is not available.
     * Calling this method multiple times will re-use the same parameter name.
     */
    final def newSyntheticValueParam(argtype: Type): Symbol =
      newSyntheticValueParams(List(argtype)).head

    /**
     * Symbol of an abstract type type T >: ... <: ...
     */
    final def newAbstractType(pos: Position, name: Name) =
      new TypeSymbol(this, pos, name.toTypeName).setFlag(DEFERRED)
    final def newAbstractType(name: Name, pos: Position = NoPosition) =
      new TypeSymbol(this, pos, name.toTypeName).setFlag(DEFERRED)

    /**
     * Symbol of a type parameter
     */
    final def newTypeParameter(pos: Position, name: Name) =
      newAbstractType(pos, name.toTypeName).setFlag(PARAM)
    final def newTypeParameter(name: Name, pos: Position = NoPosition) =
      newAbstractType(pos, name.toTypeName).setFlag(PARAM)

    /**
     * Synthetic value parameters when parameter symbols are not available
     */
    final def newSyntheticValueParamss(
        argtypess: List[List[Type]]
    ): List[List[Symbol]] = {
      var cnt             = 0
      def freshName()     = { cnt += 1; newTermName("x$" + cnt) }
      def param(tp: Type) =
        newValueParameter(NoPosition, freshName()).setFlag(SYNTHETIC)
      argtypess map (_.map(param))
    }

    final def newExistential(pos: Position, name: Name): Symbol =
      newAbstractType(pos, name.toTypeName).setFlag(EXISTENTIAL)

    def tpe: Type   = NoType
    def tpeHK: Type = tpe

    /**
     * The type constructor of a symbol is: For a type symbol, the type
     * corresponding to the symbol itself, excluding parameters. Not applicable
     * for term symbols.
     */
    def typeConstructor: Type =
      sys.error("typeConstructor inapplicable for " + this)

    final def toType: Type = typeConstructor

    def typeParams: List[Symbol]    = Nil
    def paramss: List[List[Symbol]] = Nil

    def isTerm                       = false // to be overridden
    def isType                       = false // to be overridden
    def isClass                      = false // to be overridden
    def isBottomClass                = false // to be overridden
    def isAliasType                  = false // to be overridden
    def isAbstractType               = false // to be overridden
    private[treehugger] def isSkolem = false // to be overridden

    /** Is this symbol a type but not a class? */
    def isNonClassType = false // to be overridden

    override final def isTrait     = isClass && hasFlag(TRAIT)
    final def isAbstractClass      = isClass && hasFlag(ABSTRACT)
    final def isBridge             = hasFlag(BRIDGE)
    final def isContravariant      = hasFlag(CONTRAVARIANT) // && isType
    final def isConcreteClass      = isClass && !hasFlag(ABSTRACT | TRAIT)
    final def isCovariant          = hasFlag(COVARIANT)     // && isType
    final def isEarlyInitialized   = isTerm && hasFlag(PRESUPER)
    final def isExistentiallyBound = isType && hasFlag(EXISTENTIAL)
    final def isImplClass          = isClass && hasFlag(IMPLCLASS)
    final def isLazyAccessor       = isLazy && lazyAccessor != NoSymbol
    final def isMethod             = isTerm && hasFlag(METHOD)
    final def isModule             = isTerm && hasFlag(MODULE)
    final def isModuleClass        = isClass && hasFlag(MODULE)
    final def isNumericValueClass  = definitions.isNumericValueClass(this)
    final def isOverloaded         = hasFlag(OVERLOADED)
    final def isOverridableMember  =
      !(isClass || isEffectivelyFinal) && owner.isClass
    final def isRefinementClass = isClass && name == tpnme.REFINE_CLASS_NAME
    final def isSourceMethod    =
      isMethod && !hasFlag(STABLE) // exclude all accessors!!!
    final def isTypeParameter = isType && isParameter && !isSkolem
    final def isValueClass    = definitions.isValueClass(this)
    final def isVarargsMethod = isMethod && hasFlag(VARARGS)

    /** Package tests */
    final def isEmptyPackage      = isPackage && name == nme.EMPTY_PACKAGE_NAME
    final def isEmptyPackageClass =
      isPackageClass && name == tpnme.EMPTY_PACKAGE_NAME
    final def isPackage           = isModule && hasFlag(PACKAGE)
    final def isPackageClass      = isClass && hasFlag(PACKAGE)
    final def isRoot              = isPackageClass && owner == NoSymbol
    final def isRootPackage       = isPackage && owner == NoSymbol
    final def isPredefModuleClass =
      isModuleClass && (name.toString == "Predef") && (owner.name.toString == "scala")

    /**
     * Is this symbol an effective root for fullname string?
     */
    def isEffectiveRoot = isRoot || isEmptyPackageClass || isPredefModuleClass

    /**
     * Term symbols with the exception of static parts of Java classes and
     * packages.
     */
    final def isValue = isTerm && !(isModule && hasFlag(PACKAGE | JAVA))

    final def isVariable = isTerm && isMutable && !isMethod

    final def isValueParameter       = isTerm && hasFlag(PARAM)
    final def isInitializedToDefault =
      !isType && hasAllFlags(DEFAULTINIT | ACCESSOR)
    final def isClassConstructor = isTerm && (name == nme.CONSTRUCTOR)
    final def isMixinConstructor = isTerm && (name == nme.MIXIN_CONSTRUCTOR)
    final def isError            = hasFlag(IS_ERROR)

    final def isAnonymousClass =
      isClass && (name containsName tpnme.ANON_CLASS_NAME)
    final def isAnonymousFunction =
      isSynthetic && (name containsName tpnme.ANON_FUN_NAME)
    final def isAnonOrRefinementClass = isAnonymousClass || isRefinementClass

    // A package object or its module class
    final def isPackageObjectOrClass =
      name == nme.PACKAGE || name == tpnme.PACKAGE
    final def isPackageObject      = name == nme.PACKAGE && owner.isPackageClass
    final def isPackageObjectClass =
      name == tpnme.PACKAGE && owner.isPackageClass

    final def isJavaInterface = isJavaDefined && isTrait

    /**
     * The owner, skipping package objects.
     */
    def effectiveOwner = owner.skipPackageObject

    /**
     * If this is a package object or its implementing class, its owner:
     * otherwise this.
     */
    final def skipPackageObject: Symbol =
      if (isPackageObjectOrClass) owner else this

    /**
     * Conditions where we omit the prefix when printing a symbol, to avoid
     * unpleasantries like Predef.String.
     */
    final def isOmittablePrefix = (
      UnqualifiedOwners(skipPackageObject)
        || isEmptyPrefix
    )

    def isEmptyPrefix = (
      isEffectiveRoot
        || isAnonOrRefinementClass
    )

    /**
     * The encoded full path name of this symbol, where outer names and inner
     * names are separated by `separator` characters. Never translates
     * expansions of operators back to operator symbol. Never adds id. Drops
     * package objects.
     */
    final def fullName(separator: Char): String = stripNameString(
      fullNameInternal(separator)
    )

    /**
     * Doesn't drop package objects, for those situations (e.g. classloading)
     * where the true path is needed.
     */
    private def fullNameInternal(separator: Char): String = (
      if (isRoot || isRootPackage || this == NoSymbol) this.toString
      else if (owner.isEffectiveRoot) decodedName
      else ownerNames(separator) + decodedName
    )

    final def ownerNames: String = ownerNames('.')

    final def ownerNames(separator: Char): String = (
      if (isRoot || isRootPackage || this == NoSymbol || isEffectiveRoot) ""
      else if (owner.isEffectiveRoot || owner.isRoot) ""
      else effectiveOwner.enclClass.fullName(separator) + separator
    )

    /** Is this symbol effectively final? I.e, it cannot be overridden */
    final def isEffectivelyFinal: Boolean = (
      isFinal
        || hasModuleFlag
        || isTerm && (
          isPrivate
            || isLocal
            || owner.isClass && owner.isEffectivelyFinal
        )
    )

    /**
     * Is this symbol locally defined? I.e. not accessed from outside `this`
     * instance
     */
    final def isLocal: Boolean = owner.isTerm

    /**
     * Strip package objects and any local suffix.
     */
    private def stripNameString(s: String) =
      s stripSuffix nme.LOCAL_SUFFIX_STRING

    /**
     * The encoded full path name of this symbol, where outer names and inner
     * names are separated by periods.
     */
    final def fullName: String = fullName('.')

    /** The variance of this symbol as an integer */
    final def variance: Int =
      if (isCovariant) 1
      else if (isContravariant) -1
      else 0

    final def isStructuralRefinement: Boolean =
      name == tpnme.REFINE_CLASS_NAME

// ------ owner attribute --------------------------------------------------------------

    /**
     * The owner of this symbol.
     */
    def owner: Symbol = rawowner

    def ownerChain: List[Symbol] =
      if (owner eq null) this :: Nil
      else this :: owner.ownerChain

    /**
     * The name of the symbol as a member of the `Name` type.
     */
    def name: Name = rawname

    /** The simple name of this Symbol */
    final def simpleName: Name = name

    /**
     * The name of the symbol before decoding, e.g. `\$eq\$eq` instead of `==`.
     */
    def encodedName: String = name.toString

    /**
     * The decoded name of the symbol, e.g. `==` instead of `\$eq\$eq`.
     */
    def decodedName: String = stripNameString(
      NameTransformer.decode(encodedName)
    )

    /**
     * String representation of symbol's simple name.
     */
    def nameString = decodedName

    def module: Symbol = NoSymbol

    /**
     * The module class corresponding to this module.
     */
    def moduleClass: Symbol = NoSymbol

// ------ flags attribute --------------------------------------------------------------

    final def flags: Long = {
      val fs = rawflags
      (fs | ((fs & LateFlags) >>> LateShift)) & ~(fs >>> AntiShift)
    }
    final def setFlag(mask: Long): Symbol   = withRawflags(rawflags | mask)
    final def resetFlag(mask: Long): Symbol = withRawflags(rawflags & ~mask)
    final def getFlag(mask: Long): Long     = flags & mask
    final def resetFlags(): Symbol          = withRawflags(rawflags & TopLevelCreationFlags)

    /** Does symbol have ANY flag in `mask` set? */
    final def hasFlag(mask: Long): Boolean = (flags & mask) != 0L

    /** Does symbol have ALL the flags in `mask` set? */
    final def hasAllFlags(mask: Long): Boolean = (flags & mask) == mask

    /**
     * If the given flag is set on this symbol, also set the corresponding
     * notFLAG. For instance if flag is PRIVATE, the notPRIVATE flag will be
     * set if PRIVATE is currently set.
     */
    final def setNotFlag(flag: Int): Symbol =
      if (hasFlag(flag))
        setFlag((flag: @annotation.switch) match {
          case PRIVATE   => notPRIVATE
          case PROTECTED => notPROTECTED
          case OVERRIDE  => notOVERRIDE
          case _         => sys.error("setNotFlag on invalid flag: " + flag)
        })
      else this

    /**
     * The class or term up to which this symbol is accessible, or RootClass if
     * it is public. As java protected statics are otherwise completely
     * inaccessible in scala, they are treated as public.
     */
    def accessBoundary(base: Symbol): Symbol = {
      if (hasFlag(PRIVATE) || isLocal) owner
      else if (hasAllFlags(PROTECTED | STATIC | JAVA)) RootClass
      else if (hasAccessBoundary) privateWithin
      else if (hasFlag(PROTECTED)) base
      else RootClass
    }

    /**
     * See comment in HasFlags for how privateWithin combines with flags.
     */
    final def setPrivateWithin(sym: Symbol): Symbol = withPrivateWithin(sym)

    /** Does symbol have a private or protected qualifier set? */
    final def hasAccessBoundary =
      (privateWithin != null) && (privateWithin != NoSymbol)

// ----- annotations ------------------------------------------------------------

    def annotationsString =
      if (annotations.isEmpty) "" else annotations.mkString("(", ", ", ")")

    /**
     * After the typer phase (before, look at the definition's Modifiers),
     * contains the annotations attached to member a definition (class, method,
     * type, field).
     */
    final def setAnnotations(annots: List[AnnotationInfo]): Symbol =
      copyAnnotations(annots)

    final def withAnnotations(annots: List[AnnotationInfo]): Symbol =
      copyAnnotations(annots ::: annotations)

    final def withoutAnnotations: Symbol = copyAnnotations(Nil)

    final def filterAnnotations(p: AnnotationInfo => Boolean): Symbol =
      copyAnnotations(annotations filter p)

    final def addAnnotation(annot: AnnotationInfo): Symbol =
      copyAnnotations(annot :: annotations)

    final def addAnnotation(sym: Symbol, args: Tree*): Symbol =
      copyAnnotations(AnnotationInfo(sym.tpe, args.toList, Nil) :: annotations)

// ------ comparisons ----------------------------------------------------------------

    /** Is this class symbol a subclass of that symbol? */
    final def isNonBottomSubClass(that: Symbol): Boolean = (
      (this eq that) || this.isError || that.isError
    )

    /**
     * Overridden in NullClass and NothingClass for custom behavior.
     */
    def isSubClass(that: Symbol) = isNonBottomSubClass(that)

// ------ access to related symbols --------------------------------------------------

    /** The next enclosing class. */
    def enclClass: Symbol = if (isClass) this else owner.enclClass

    /**
     * If symbol is a class, the type <code>this.type</code> in this class,
     * otherwise <code>NoPrefix</code>. We always have: thisType <:< typeOfThis
     */
    def thisType: Type = NoPrefix

    /**
     * The module corresponding to this module class (note that this is not
     * updated when a module is cloned), or NoSymbol if this is not a
     * ModuleClass.
     */
    def sourceModule: Symbol = NoSymbol

    /** For a lazy value, its lazy accessor. NoSymbol for all others. */
    def lazyAccessor: Symbol = NoSymbol

// ------ toString -------------------------------------------------------------------

    /** String representation of symbol's definition key word */
    final def keyString: String =
      if (isJavaInterface) "interface"
      else if (isTrait) "trait"
      else if (isClass) "class"
      else if (isType && !isParameter) "type"
      else if (isVariable) "var"
      else if (isPackage) "package"
      else if (isModule) "object"
      else if (isSourceMethod) "def"
      else if (isTerm && (!isParameter || isParamAccessor)) "val"
      else ""

    override def toString = nameString

    def signatureString =
      "<_>"

    def hasFlagsToString(mask: Long): String = flagsToString(
      flags & mask,
      if (hasAccessBoundary) privateWithin.toString else ""
    )

    /** String representation of symbol's variance */
    def varianceString: String =
      if (variance == 1) "+"
      else if (variance == -1) "-"
      else ""

    def defaultFlagMask =
      if (owner.isRefinementClass) ExplicitFlags & ~OVERRIDE
      else ExplicitFlags

    def accessString      = hasFlagsToString(PRIVATE | PROTECTED | LOCAL)
    def defaultFlagString = hasFlagsToString(defaultFlagMask)

    private def defStringCompose(infoString: String) = compose(
      defaultFlagString,
      keyString,
      varianceString + nameString + infoString
    )

    /**
     * String representation of symbol's definition. It uses the symbol's raw
     * info to avoid forcing types.
     */
    def defString = defStringCompose(signatureString)

    /** Concatenate strings separated by spaces */
    private def compose(ss: String*) = ss filter (_ != "") mkString " "

    def isSingletonExistential = false

    /** String representation of existentially bound variable */
    def existentialToString = defString
  }

// ------ TermSymbol ---------------------------------------------------------------

  /** A class for term symbols */
  class TermSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TermName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil,
      val referenced: Symbol = NoSymbol
  ) extends Symbol(initOwner, initPos, initName, initFlags, initPrivateWithin, initAnnotations) {

    final override def isTerm = true

    override def name: TermName = super.name.asInstanceOf[TermName]

    def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TermName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations,
        referenced: Symbol = this.referenced
    ): TermSymbol =
      new TermSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations, referenced)

    override protected def withRawflags(f: Long): TermSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): TermSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): TermSymbol =
      copy(annotations = a)

    override def moduleClass: Symbol =
      if (hasFlag(MODULE)) referenced
      else NoSymbol

    def setModuleClass(clazz: Symbol): TermSymbol = {
      assert(hasFlag(MODULE))
      copy(referenced = clazz)
    }
  }

// ------ ModuleSymbol -------------------------------------------------------------

  /** A class for module symbols */
  class ModuleSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TermName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil,
      initReferenced: Symbol = NoSymbol
  ) extends TermSymbol(
        initOwner,
        initPos,
        initName,
        initFlags,
        initPrivateWithin,
        initAnnotations,
        initReferenced
      ) {

    override def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TermName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations,
        referenced: Symbol = this.referenced
    ): ModuleSymbol =
      new ModuleSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations, referenced)

    override protected def withRawflags(f: Long): ModuleSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): ModuleSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): ModuleSymbol =
      copy(annotations = a)

    override def setModuleClass(clazz: Symbol): ModuleSymbol = {
      assert(hasFlag(MODULE))
      copy(referenced = clazz)
    }
  }

// ------ MethodSymbol -------------------------------------------------------------

  /** A class for method symbols */
  class MethodSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TermName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil
  ) extends TermSymbol(
        initOwner,
        initPos,
        initName,
        initFlags,
        initPrivateWithin,
        initAnnotations
      ) {

    override def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TermName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations,
        referenced: Symbol = this.referenced
    ): MethodSymbol =
      new MethodSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations)

    override protected def withRawflags(f: Long): MethodSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): MethodSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): MethodSymbol =
      copy(annotations = a)
  }

// ------ TypeSymbol ---------------------------------------------------------------

  class TypeSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TypeName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil
  ) extends Symbol(initOwner, initPos, initName, initFlags, initPrivateWithin, initAnnotations) {

    override def name: TypeName = super.name.asInstanceOf[TypeName]
    final override def isType   = true
    override def isNonClassType = true

    private def newTypeRef(targs: List[Type]) = {
      val pre = if (hasFlag(PARAM | EXISTENTIAL)) NoPrefix else owner.thisType
      typeRef(pre, this, targs)
    }

    override lazy val typeConstructor: Type = newTypeRef(Nil)

    override def tpeHK = typeConstructor

    def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TypeName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations
    ): TypeSymbol =
      new TypeSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations)

    override protected def withRawflags(f: Long): TypeSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): TypeSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): TypeSymbol =
      copy(annotations = a)
  }

// ------ ClassSymbol --------------------------------------------------------------

  /** A class for class symbols */
  class ClassSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TypeName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil
  ) extends TypeSymbol(
        initOwner,
        initPos,
        initName,
        initFlags,
        initPrivateWithin,
        initAnnotations
      ) {

    final override def isClass        = true
    final override def isNonClassType = false
    final override def isAbstractType = false
    final override def isAliasType    = false

    /** the type this.type in this class */
    override lazy val thisType: Type = ThisType(this)

    override lazy val module = new ModuleSymbol(rawowner, rawpos, rawname.toTermName)

    override def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TypeName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations
    ): ClassSymbol =
      new ClassSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations)

    override protected def withRawflags(f: Long): ClassSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): ClassSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): ClassSymbol =
      copy(annotations = a)
  }

// ------ ModuleClassSymbol --------------------------------------------------------

  /**
   * A class for module class symbols Note: Not all module classes are of this
   * type; when unpickled, we get plain class symbols!
   */
  class ModuleClassSymbol(
      initOwner: Symbol,
      initPos: Position,
      initName: TypeName,
      initFlags: Long = 0L,
      initPrivateWithin: Symbol = null,
      initAnnotations: List[AnnotationInfo] = Nil
  ) extends ClassSymbol(
        initOwner,
        initPos,
        initName,
        initFlags,
        initPrivateWithin,
        initAnnotations
      ) {

    def this(module: TermSymbol) =
      this(
        module.rawowner,
        module.rawpos,
        module.name.toTypeName,
        module.getFlag(ModuleToClassFlags) | MODULE
      )

    override def copy(
        rawowner: Symbol = this.rawowner,
        rawpos: Position = this.rawpos,
        rawname: TypeName = this.name,
        rawflags: Long = this.rawflags,
        privateWithin: Symbol = this.privateWithin,
        annotations: List[AnnotationInfo] = this.annotations
    ): ModuleClassSymbol =
      new ModuleClassSymbol(rawowner, rawpos, rawname, rawflags, privateWithin, annotations)

    override protected def withRawflags(f: Long): ModuleClassSymbol =
      copy(rawflags = f)
    override protected def withPrivateWithin(pw: Symbol): ModuleClassSymbol =
      copy(privateWithin = pw)
    override protected def copyAnnotations(a: List[AnnotationInfo]): ModuleClassSymbol =
      copy(annotations = a)
  }

// ------ NoSymbol -----------------------------------------------------------------

  object NoSymbol extends Symbol(null, NoPosition, nme.NO_NAME, 0L, null, Nil) {
    override protected def withRawflags(f: Long): Symbol                    = this
    override protected def withPrivateWithin(pw: Symbol): Symbol            = this
    override protected def copyAnnotations(a: List[AnnotationInfo]): Symbol = this
  }
}
