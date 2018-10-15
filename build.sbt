name := "hablapps"

scalaVersion := "2.12.6"

scalaBinaryVersion := "2.12"

organization := "org.hablapps"

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")

addCompilerPlugin("org.scalamacros" %% "paradise" % "2.1.0" cross CrossVersion.full)

enablePlugins(TutPlugin)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.0.0",
  "com.chuusai" %% "shapeless" % "2.3.2",
  "org.scalaz" %% "scalaz-core" % "7.2.7"
)

scalacOptions ++= Seq(
  "-unchecked",
  "-deprecation",
  "-Ypartial-unification",
  // "-Xprint:typer",
  // "-Xlog-implicit-conversions",
  "-explaintypes",
  "-feature",
  "-language:implicitConversions",
  "-language:postfixOps",
  "-language:higherKinds")
