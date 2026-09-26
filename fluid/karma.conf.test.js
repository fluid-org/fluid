module.exports = function (config) {
   config.set({
      autoWatch: true,
      basePath: "",
      browsers: ["ChromeHeadlessNoSandbox"],
      browserDisconnectTimeout: 600000,
      browserNoActivityTimeout: 2400000,
      customLaunchers: {
         ChromeHeadlessNoSandbox: {
           base: 'ChromeHeadless',
            flags: [
               '--disable-gpu',
               '--no-sandbox'
            ]
         }
      },
      client: {
         mocha: {
            timeout: 600000
         }
      },
      colors: true,
      failOnEmptyTestSuite: true,
      files: [
         "./dist/test/fluid.js",
         {
            pattern: "./lib/**/*.fld",
            watched: true,
            included: false,
            served: true,
            nocache: false
         },
         {
            pattern: "./test/**/*.*",
            watched: true,
            included: false,
            served: true,
            nocache: false,
         }
      ],
      frameworks: ["mocha"],
      logLevel: config.LOG_ERROR,
      proxies: {
         "/lib/": "/base/lib/",
         "/dataset/": "/base/test/dataset/",
         "/test/fluid/": "/base/test/fluid/"
      },
      reporters: ["mocha"],
      singleRun: true
   })
}
