ThisBuild / scalaVersion := "2.13.7"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "com.example"
ThisBuild / organizationName := "precondition"

resolvers += "jitpack" at "https://jitpack.io"

val catsV = "2.7.0"
val typesAndcatsDeps = Seq(
  "org.typelevel"              %% "cats-core" % catsV,
  "org.typelevel"              %% "cats-free" % catsV,
  "com.github.doofin.stdScala" %% "stdscala"  % "c9d19a6db3"
)

unmanagedJars in Compile ++= Seq("com.microsoft.z3.jar").map( //"scalaz3-unix-x64-2.12.jar"
  x => file("lib/" + x)
)

lazy val root = (project in file("."))
  .settings(
    name := "pre_expectation",
    libraryDependencies ++= Seq("org.scalatest" %% "scalatest-funsuite" % "3.2.9") ++ typesAndcatsDeps
  )
