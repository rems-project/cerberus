const merge = require('webpack-merge');
const baseConfig = require('./base.config.js');

module.exports = merge(baseConfig, {
  mode: 'production',
  optimization: {
    splitChunks: {
      cacheGroups: {
        commons: {
          test: /[\\/]node_modules\/vis[\\/]/,
          name: 'vis',
          chunks: 'all',
        },
        commons2: {
          test: /[\\/]node_modules\/codemirror[\\/]/,
          name: 'codemirror',
          chunks: 'all',
        },
      },
    },
  },
});

